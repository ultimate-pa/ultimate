# This file can be used as benchexec tool info module to run arbitrary commands
# and scan the produced output to determine the result.
# For instance, combine it with ./run-test.sh to run individual unit tests with benchexec.
#
# As an example, see the usage in ./benchexec/og-proof-generation.xml .

import benchexec.tools.template
import benchexec.result as result
import logging
import re

class Tool(benchexec.tools.template.BaseTool2):
    """
    """

    def executable(self, tool_locator):
        return tool_locator.find_executable("run-test.sh")

    def name(self):
        return "shell"

    def cmdline(self, executable, options, task, rlimits):
        success_index = options.index('success')
        self.success = options[success_index + 1]
        failure_index = options.index('failure')
        self.failure = options[failure_index + 1]
        command_index = options.index('command')
        command = options[command_index + 1]
        return command.split(' ')

    def determine_result(self, run):
        for line in run.output:
            if re.search(self.success, line) is not None:
                return result.RESULT_DONE
            if re.search(self.failure, line) is not None:
                return result.RESULT_ERROR
        return result.RESULT_UNKNOWN

    def get_value_from_output(self, output, identifier):
        regex = re.compile(identifier)
        for line in output:
            match = regex.search(line)
            if match and len(match.groups()) > 0:
                return match.group(1)
        logging.debug("Did not find a match with regex %s", identifier)
        return None
