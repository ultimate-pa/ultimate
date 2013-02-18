package local.stalin.core.api;

import java.io.File;

import local.stalin.core.coreplugin.Activator;

import org.apache.log4j.Logger;

public class PreludeProvider {

	private File prelude;
	
	public PreludeProvider(String preludefile) {
		// get the logger of the core
		Logger s_logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
		if (preludefile != null) {
			File foo = new File(preludefile);
			// prelude file must exist and must be readable
			if (!foo.exists()) {
				s_logger.error("Prelude file "+preludefile+" doesn't exist! It will be ignored when processing the toolchain!");
				prelude = null;
			} else {
				if (!foo.canRead()) {
					s_logger.error("Prelude file "+preludefile+" is not readable! It will be ignored when processing the toolchain!");
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
