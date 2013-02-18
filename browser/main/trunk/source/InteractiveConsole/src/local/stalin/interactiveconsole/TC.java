package local.stalin.interactiveconsole;

import java.util.List;

import local.stalin.core.coreplugin.toolchain.Toolchain;
import local.stalin.ep.interfaces.ITool;

/**
 * Mother class for the intermediate parser representation of a toolchain.
 * 
 * @author Christian Simon
 *
 */
abstract class TC {

	/**
	 * The name says it all.
	 * 
	 * @param tools, list of available tools
	 * @return toolchain stored in class will be returned 
	 * as a valid Toolchain object that can be processed 
	 * by the core, 'null' says that the old toolchain 
	 * shall be maintained
	 * 
	 */
	public abstract Toolchain getToolchain(List<ITool> tools) throws Exception;
}
