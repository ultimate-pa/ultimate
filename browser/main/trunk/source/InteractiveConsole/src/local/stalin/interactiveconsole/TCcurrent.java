package local.stalin.interactiveconsole;

import java.util.List;

import local.stalin.core.coreplugin.toolchain.Toolchain;
import local.stalin.ep.interfaces.ITool;

/**
 * Represents 'current' toolchain.
 * 
 * @author Christian Simon
 *
 */
public class TCcurrent extends TC {


	@Override
	public Toolchain getToolchain(List<ITool> tools) throws Exception {
		// simply return null
		// the caller will know what to do then
		return null;
	}

}
