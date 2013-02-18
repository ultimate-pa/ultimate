package local.stalin.interactiveconsole;

import java.util.List;

import local.stalin.core.coreplugin.toolchain.Toolchain;
import local.stalin.ep.interfaces.ITool;

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
	public Toolchain getToolchain(List<ITool> tools) throws Exception {
		Toolchain foo = new Toolchain();
		foo.addPlugin(tools.get(Integer.valueOf(number)).getPluginID());
		if (next != null)
			foo.addToolchain(next.getToolchain(tools));
		return foo;
	}
	
}
