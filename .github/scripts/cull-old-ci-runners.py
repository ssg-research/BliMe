#!/usr/bin/env python3

# Runs periodically in it's own workflow in the CI/CD environment to teardown
# runners that are offline

from common import deregister_offline_runners

# Reuse manager utilities
from ci_variables import ci_personal_api_token

def main():
    # deregister all offline runners
    deregister_offline_runners(ci_personal_api_token)

if __name__ == "__main__":
    main()
