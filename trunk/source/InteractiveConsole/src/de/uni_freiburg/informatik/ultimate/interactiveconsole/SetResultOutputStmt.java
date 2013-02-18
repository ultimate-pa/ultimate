package de.uni_freiburg.informatik.ultimate.interactiveconsole;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.plugins.ResultNotifier;

public class SetResultOutputStmt extends Stmt {

	private String filename;
	
	public SetResultOutputStmt(String filename) {
		this.filename = filename;
	}
	
	@Override
	public void execute() {
		try {
			ResultNotifier.setResultWriter(new PrintWriter(new FileWriter(filename)));
		} catch (IOException ioexc) {
			ioexc.printStackTrace(System.err);
		}
	}

}
