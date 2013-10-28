package de.uni_freiburg.informatik.ultimate.interactiveconsole;


public class SetResultOutputStmt extends Stmt {

	private String filename;
	
	public SetResultOutputStmt(String filename) {
		this.filename = filename;
	}
	
	@Override
	public void execute() {
		//TODO: Config log4j such that logs are written to file 
//			ResultNotifier.setResultWriter(new PrintWriter(new FileWriter(filename)));
		System.err.println("Config log4j such that logs are written to file ");
	}

}
