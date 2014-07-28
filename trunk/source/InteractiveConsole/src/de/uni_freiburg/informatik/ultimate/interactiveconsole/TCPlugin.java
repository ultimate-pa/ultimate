package de.uni_freiburg.informatik.ultimate.interactiveconsole;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

/**
 * Representation for a plugin.
 * 
 * @author Christian Simon
 *
 */
public class TCPlugin extends TCnew {

	private String number;
	private TCnew next;
	
	
	/**
	 * @param name of the plugin
	 * @param pointer to next elem in chain
	 */
	public TCPlugin(String name, TCnew next) {
		this.number = name;
		this.next = next;
	}

	@Override
	public ToolchainData getToolchain(List<ITool> tools) throws Exception {
		ToolchainData foo = new ToolchainData();
		foo.addPlugin(tools.get(Integer.valueOf(number)).getPluginID());
		if (next != null)
			foo.addToolchain(next.getToolchain(tools));
		return foo;
	}
	
}
