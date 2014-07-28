package de.uni_freiburg.informatik.ultimate.interactiveconsole;

/**
 * Statement that is responsible for outputting a list of models stored in
 * Ultimate.
 * 
 * @author Christian Simon
 * @deprecated Seems unused. Will not be replaced if no one needs it
 */
public class ListMMStmt extends Stmt {

	@Override
	public void execute() {
		throw new UnsupportedOperationException();
		// TODO: After refactoring for IUltimateServiceProvider, those methods
		// are not provided anymore. It is unclear if someone actually uses the
		// InteractiveConsole, so I prepared this here to die

		// List<String> modellist = this.controller.getModelList();
		// System.out.println("Index\tDescription");
		// for (int i=0; i<modellist.size(); i++) {
		// System.out.println(String.valueOf(i)+"\t"+modellist.get(i));
		// }

	}

}
