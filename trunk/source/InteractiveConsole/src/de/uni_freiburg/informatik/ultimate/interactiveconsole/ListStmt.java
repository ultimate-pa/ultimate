package de.uni_freiburg.informatik.ultimate.interactiveconsole;

/**
 * Statement that is responsible for outputting a list of plugins.
 * 
 * @author Christian Simon
 * @deprecated Seems unused. Will not be replaced if no one needs it
 */
class ListStmt extends Stmt {
	public ListStmt() {
	}

	@Override
	public void execute() {
		throw new UnsupportedOperationException();
		// TODO: After refactoring for IUltimateServiceProvider, those methods
		// are not provided anymore. It is unclear if someone actually uses the
		// InteractiveConsole, so I prepared this here to die
		//
		// List<ITool> foo = this.controller.getTools();
		// System.out.println("Index\tPlugin-ID");
		// for (int i = 0; i < foo.size(); i++) {
		// System.out.println(String.valueOf(i)+"\t"+foo.get(i).getPluginID());
		// }
	}
}
