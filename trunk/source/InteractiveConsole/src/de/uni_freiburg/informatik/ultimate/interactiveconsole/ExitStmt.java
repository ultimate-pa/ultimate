package de.uni_freiburg.informatik.ultimate.interactiveconsole;

/**
 * Exit Interactive Console
 * 
 * @author Christian Simon
 *
 */
class ExitStmt extends Stmt {
	public ExitStmt () {
	}

	@Override
	public void execute() {
		this.controller.m_CancelRequest = true;
	}
}
