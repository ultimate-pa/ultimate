# All things logging.

import logging

__DEBUG_LEVEL_IO__ = 5

def initialize_logger(verbose):
    "Initializes the logging system"
    logging.basicConfig(level=verbose)
#     logging.basicConfig(level=logging.DEBUG)
    logging.addLevelName(__DEBUG_LEVEL_IO__, "DEBUG I/O")

    root = logging.getLogger()

    hdlr = root.handlers[0]    
    if root.getEffectiveLevel() < logging.DEBUG:
        formatter = logging.Formatter("%(asctime)s - %(levelname)s (%(name)s) - %(message)s")
    else:
        formatter = logging.Formatter("%(levelname)s: %(message)s")
    
    hdlr.setFormatter(formatter)
    logging.debug("Logger initialized with level " + str(logging.getLevelName(logging.getLogger().getEffectiveLevel())))

def debugio(message, *args, **kws):
    "Logs debug information for I/O operations."
    if logging.getLogger().isEnabledFor(__DEBUG_LEVEL_IO__):
        logging.getLogger()._log(__DEBUG_LEVEL_IO__, message, args, **kws)