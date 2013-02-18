package de.uni_freiburg.informatik.ultimate.interactiveconsole;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.SubchainType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

/**
 * Representation for a Subchain.
 * 
 * @author Christian Simon
 *
 */
public class TCSubchain extends TCnew {

	private TCnew next;
	private TCnew subchain;

	/**
	 * @param pointer to toolchain making up the subchain
	 * @param pointer to next element in chain
	 */
	public TCSubchain(TCnew sbc, TCnew next) {
		this.subchain = sbc;
		this.next = next;
	}

	@Override
	public Toolchain getToolchain(List<ITool> tools) throws Exception {
		Toolchain foo = new Toolchain();
		Toolchain bar = subchain.getToolchain(tools);
		SubchainType ct = new SubchainType();
		ct.getPluginOrSubchain().addAll(bar.getToolchain().getPluginOrSubchain());
		foo.addSubchain(ct);
		if (next != null)
			foo.addToolchain(next.getToolchain(tools));
		return foo;
	}
	
}
