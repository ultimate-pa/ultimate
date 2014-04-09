package de.uni_freiburg.informatik.ultimate.interactiveconsole;

public class LoadPrefsStmt extends Stmt {

	private String m_Filename;
	
	public LoadPrefsStmt(String filename) {
		m_Filename = filename;
	}
	
	@Override
	public void execute() {
		controller.getCore().loadPreferences(m_Filename);
	}

}
