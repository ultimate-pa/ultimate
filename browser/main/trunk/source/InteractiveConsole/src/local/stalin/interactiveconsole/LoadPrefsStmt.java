package local.stalin.interactiveconsole;

public class LoadPrefsStmt extends Stmt {

	private String m_Filename;
	
	public LoadPrefsStmt(String filename) {
		m_Filename = filename;
	}
	
	@Override
	public void execute() {
		controller.setPrefFile(m_Filename);
		controller.getCore().loadPreferences();
	}

}
