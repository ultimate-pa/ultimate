package de.uni_freiburg.informatik.ultimate.interactiveconsole;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

/**
 * Represents 'current' toolchain.
 * 
 * @author Christian Simon
 *
 */
public class TCcurrent extends TC {


	@Override
	public ToolchainData getToolchain(List<ITool> tools) throws Exception {
		// simply return null
		// the caller will know what to do then
		return null;
	}

}
