package de.uni_freiburg.informatik.ultimate.core.services;

import java.io.File;
import org.apache.log4j.Logger;

public class PreludeProvider {

	private File prelude;
	
	public PreludeProvider(String preludefile, Logger logger) {
		// get the logger of the core
		if (preludefile != null) {
			File foo = new File(preludefile);
			// prelude file must exist and must be readable
			if (!foo.exists()) {
				logger.error("Prelude file "+preludefile+" doesn't exist! It will be ignored when processing the toolchain!");
				prelude = null;
			} else {
				if (!foo.canRead()) {
					logger.error("Prelude file "+preludefile+" is not readable! It will be ignored when processing the toolchain!");
					prelude = null;
				} else {
					this.prelude = foo;
				}
			}
		} else {
			this.prelude = null;
		}
	}
	
	public File getPreludeFile() {
		return this.prelude;
	}
	
}
