/*
 * Copyright (c) 2017 Jason Lowe-Power
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met: redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer;
 * redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution;
 * neither the name of the copyright holders nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "mem/taint_fetch_merge.hh"

#include <random>

#include "base/trace.hh"
#include "debug/TaintFetchMerge.hh"

namespace gem5
{

namespace memory
{

// NOTE: revert this to 0x81000000 - 0xC0000000 for x86
#define MEM_BEGIN 0x80000000
// #define ADDRESSABLE_MEM_SIZE 0x1C0000000
// #define TAINT_SIZE 0x40000000
#define ADDRESSABLE_MEM_SIZE 0x200000000
#define TAINT_SIZE 0x200000000

TaintFetchMerge::TaintFetchMerge(const TaintFetchMergeParams &params) :
    SimObject(params),
    cpuPort(params.name + ".cpu_side", this),
    memPort(params.name + ".mem_side", this),
    blocked(false)
{
    DPRINTF(TaintFetchMerge,
        "Created TaintFetchMerge object: %s\n", params.name);
}

Port &
TaintFetchMerge::getPort(const std::string &if_name, PortID idx)
{
    panic_if(idx != InvalidPortID, "This object doesn't support vector ports");

    // This is the name from the Python SimObject decl (TaintFetchMerge.py)
    if (if_name == "mem_side") {
        return memPort;
    } else if (if_name == "cpu_side") {
        return cpuPort;
    } else {
        // pass it along to our super class
        return SimObject::getPort(if_name, idx);
    }
}

bool
TaintFetchMerge::CPUSidePort::sendPacket(PacketPtr pkt)
{
    // Note: This flow control is very simple since the memobj is blocking.

    // panic_if(blockedPacket != nullptr,
    //      "[CPUSidePort] Should never try to send if blocked!");

    // If we can't send the packet across the port, store it for later.
    // if (!sendTimingResp(pkt)) {
    //     blockedPacket = pkt;
    // }
    return sendTimingResp(pkt);
}

AddrRangeList
TaintFetchMerge::CPUSidePort::getAddrRanges() const
{
    return owner->getAddrRanges();
}

void
TaintFetchMerge::CPUSidePort::trySendRetry()
{
    if (needRetry) {
        // Only send a retry if the port is now completely free
        needRetry = false;
        DPRINTF(TaintFetchMerge, "Sending retry req for %d\n", id);
        sendRetryReq();
    }
}

void
TaintFetchMerge::CPUSidePort::recvFunctional(PacketPtr pkt)
{
    // Just forward to the memobj.
    return owner->handleFunctional(pkt);
}

bool
TaintFetchMerge::CPUSidePort::recvTimingReq(PacketPtr pkt)
{
    // Just forward to the memobj.
    if (!owner->handleRequest(pkt)) {
        needRetry = true;
        return false;
    } else {
        return true;
    }
}

void
TaintFetchMerge::CPUSidePort::recvRespRetry()
{
    // We should have a blocked packet if this function is called.
    // assert(blockedPacket != nullptr);

    // Grab the blocked packet.
    // PacketPtr pkt = blockedPacket;
    // blockedPacket = nullptr;

    // Try to resend it. It's possible that it fails again.
    // sendPacket(pkt);
    owner->fwdRespRetry();
}

Tick
TaintFetchMerge::CPUSidePort::recvAtomic(PacketPtr pkt)
{
    DPRINTF(TaintFetchMerge,
        "[CPUSidePort] Got ATOMIC request for addr %#x. Packet: %s\n",
        pkt->getAddr(), pkt->print());
    return owner->handleAtomic(pkt);
}

void
TaintFetchMerge::MemSidePort::sendTwoPackets(PacketPtr taint_pkt,
                                             PacketPtr pkt)
{
    panic_if(blockedTaintPacket != nullptr,
        "[MemSidePort] Should never try to send if blocked! 1");
    panic_if(blockedPacket != nullptr,
        "[MemSidePort] Should never try to send if blocked! 2");

    // If we can't send the packet across the port, store it for later.
    if (taint_pkt && !sendTimingReq(taint_pkt)) {
        blockedTaintPacket = taint_pkt;
        blockedPacket = pkt;
        return;
    }
    if (!sendTimingReq(pkt)) {
        blockedTaintPacket = nullptr;
        blockedPacket = pkt;
        return;
    }

    blockedTaintPacket = nullptr;
    blockedPacket = nullptr;
    owner->unblock();
}

bool
TaintFetchMerge::MemSidePort::recvTimingResp(PacketPtr pkt)
{
    // Just forward to the memobj.
    return owner->handleResponse(pkt);
}

void
TaintFetchMerge::MemSidePort::recvReqRetry()
{
    // We should have a blocked packet if this function is called.
    assert(blockedPacket != nullptr || blockedTaintPacket != nullptr);

    // Grab the blocked packet(s). taint_pkt could be a nullptr.
    PacketPtr taint_pkt = blockedTaintPacket;
    blockedTaintPacket = nullptr;
    PacketPtr pkt = blockedPacket;
    blockedPacket = nullptr;

    // Try to resend it. It's possible that it fails again.
    sendTwoPackets(taint_pkt, pkt);
}

void
TaintFetchMerge::MemSidePort::recvRangeChange()
{
    owner->sendRangeChange();
}

bool
TaintFetchMerge::handleRequest(PacketPtr pkt)
{
    if (blocked) {
        // There is currently an outstanding request. Stall.
        return false;
    }

    DPRINTF(TaintFetchMerge,
        "Got request for addr %#x. Packet: %s\n",
        pkt->getAddr(), pkt->print());

    // This memobj is now blocked waiting for the response to this packet.
    blocked = true;

    assert(pkt->getSize() % 8 == 0);
    // unsigned int taintPktSize = pkt->getSize() / 8;
    unsigned int taintPktSize = pkt->getSize();

    // Addr taintAddr = 0x81000000; // fixed addr for now; FIXME
    // Addr taintAddr = distrib(gen);

    const Addr taintBegin = MEM_BEGIN + ADDRESSABLE_MEM_SIZE;
    // Addr taintAddr = (pkt->getAddr() - MEM_BEGIN) / 8 + taintBegin;
    Addr taintAddr = (pkt->getAddr() - MEM_BEGIN) + taintBegin;
    bool taintAddrInRange = false;
    for (auto addrRange : memPort.getAddrRanges()) {
        if (addrRange.contains(taintAddr)) {
            taintAddrInRange = true;
            break;
        }
    }
    if (!taintAddrInRange) {
        DPRINTF(TaintFetchMerge,
            "Taint addr %#x not in range. Adjusting.\n", pkt->getAddr());
        taintAddr += 64;
        for (auto addrRange : memPort.getAddrRanges()) {
            if (addrRange.contains(taintAddr)) {
                taintAddrInRange = true;
                break;
            }
        }
    }
    panic_if(!taintAddrInRange,
        "Taint address not in range even after adjustment!!\n");

    RequestPtr taint_req = std::make_shared<Request>(
            taintAddr, taintPktSize, 0, 1);
    PacketPtr taint_pkt = nullptr;

    if (pkt->isWrite()) {
        taint_pkt = new Packet(taint_req, MemCmd::WriteReq, taintPktSize);
        uint8_t *data = new uint8_t[taintPktSize];
        memset(data, 0, taintPktSize * sizeof(uint8_t));
        taint_pkt->dataDynamic(data);
    } else {
        taint_pkt = new Packet(taint_req, MemCmd::ReadReq, taintPktSize);
        taint_pkt->allocate();
    }


    // Forward to the memory port
    assert(taint_pkt != nullptr && pkt != nullptr);
    memPort.sendTwoPackets(taint_pkt, pkt);

    // return true even if blocked is true because we have received
    // the original request and are currently processing it; we will
    // unblock when memPort is freed
    return true;
}

bool
TaintFetchMerge::handleResponse(PacketPtr pkt)
{
    // assert(blocked);
    DPRINTF(TaintFetchMerge, "Got response for addr %#x\n", pkt->getAddr());

    // The packet is now done. We're about to put it in the port, no need for
    // this object to continue to stall.
    // We need to free the resource before sending the packet in case the CPU
    // tries to send another request immediately (e.g., in the same callchain).
    // blocked = false;

    // NOTE: revert this to 0x81000000 - 0xC0000000 for x86
    // if (pkt->req->hasPaddr() &&
    //      pkt->req->getPaddr() >= 0x81000000 &&
    //      pkt->req->getPaddr() < 0xC0000000)
    const Addr taintBegin = MEM_BEGIN + ADDRESSABLE_MEM_SIZE;
    if (pkt->req->hasPaddr() &&
        pkt->req->getPaddr() >= taintBegin &&
        pkt->req->getPaddr() < (taintBegin + TAINT_SIZE))
    {
        // this is a taint response packet
        // throw it away for now
        delete pkt;
        return true;
    } else {
        // Simply forward to the cpu port
        return cpuPort.sendPacket(pkt);
    }

    panic_if(true, "Should never reach this!\n");
}

void
TaintFetchMerge::fwdRespRetry()
{
    memPort.sendRetryResp();
}

void
TaintFetchMerge::handleFunctional(PacketPtr pkt)
{
    // Just pass this on to the memory side to handle for now.
    memPort.sendFunctional(pkt);
}

Tick
TaintFetchMerge::handleAtomic(PacketPtr pkt)
{
    // Just pass this on to the memory side to handle for now.
    return memPort.sendAtomic(pkt);
}

AddrRangeList
TaintFetchMerge::getAddrRanges() const
{
    DPRINTF(TaintFetchMerge, "Sending new ranges\n");
    // Just use the same ranges as whatever is on the memory side.
    return memPort.getAddrRanges();
}

void
TaintFetchMerge::sendRangeChange()
{
    cpuPort.sendRangeChange();
}

void
TaintFetchMerge::unblock()
{
    blocked = false;

    // For the cpu port, if it needs to send a retry, it should do it
    // since this object is unblocked now.
    cpuPort.trySendRetry();
}

} // namespace memory

} // namespace gem5
