package local.stalin.SMTInterface.preferences.nativez3;

import java.util.StringTokenizer;

import local.stalin.SMTInterface.Activator;
import local.stalin.core.api.StalinServices;
import local.stalin.nativez3.Z3Config;
import local.stalin.nativez3.Z3Exception;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;

public class Z3ConfigConfigurator {

	public static void configure(Z3Config cfg) throws Z3Exception {
		Logger logger = StalinServices.getInstance().getLoggerForExternalTool("Z3Configurator");
		InstanceScope scope = new InstanceScope();
		IEclipsePreferences prefs = scope.getNode(Activator.PLUGIN_ID);
		String cval = prefs.get(PreferenceInitializer.NATIVEZ3CONFIG, "");
//		System.err.println("Retrived Native Z3 config: " + cval);
		StringTokenizer tok = new StringTokenizer(cval,
				PreferenceInitializer.SEPARATOR);
		while (tok.hasMoreTokens()) {
			String keyval = tok.nextToken();
			int idx = keyval.indexOf("=");
			String key = keyval.substring(0, idx);
			String val = keyval.substring(idx + 1);
			logger.info("Setting Z3 configuration " + keyval);
			cfg.setConfig(key, val);
		}
		// Prevent term simplification and modification of formula like:
		// (- a b) ~> (+ a (* -1 b))
		// -x ~> (* -1 x)
//		cfg.setConfig("PRE_SIMPLIFIER", "false");
//		cfg.setConfig("PRE_SIMPLIFY_EXPR", "false");
	}
}
