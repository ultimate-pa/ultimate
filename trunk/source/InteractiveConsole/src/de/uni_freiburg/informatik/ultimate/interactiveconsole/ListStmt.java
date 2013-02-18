package de.uni_freiburg.informatik.ultimate.interactiveconsole;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

/**
 * Statement that is responsible for outputting a list of plugins.
 * 
 * @author Christian Simon
 *
 */
class ListStmt extends Stmt {
	public ListStmt () {
	}

	@Override
	public void execute() {
		List<ITool> foo = this.controller.getTools();
		System.out.println("Index\tPlugin-ID");
		for (int i = 0; i < foo.size(); i++) {
			System.out.println(String.valueOf(i)+"\t"+foo.get(i).getPluginID());
		}
	}
}
