// See LICENSE for license details.

package midas.core

import chisel3._
import chisel3.util._
import freechips.rocketchip.amba.axi4._
import freechips.rocketchip.config.{Parameters, Field}
import freechips.rocketchip.diplomacy._

import midas.widgets._

/**
  * This is a stub to foreshadow the other implementation
  */
class FPGAManagedStreamEngine(p: Parameters, val params: StreamEngineParameters) extends StreamEngine(p) {
  val cpuManagedAXI4NodeOpt = None
  val fpgaManagedAXI4NodeOpt = Some(midas.widgets.AXI4TieOff()(p))

  lazy val module = new WidgetImp(this) {
    val io = IO(new WidgetIO)
    genCRFile()
  }
}
