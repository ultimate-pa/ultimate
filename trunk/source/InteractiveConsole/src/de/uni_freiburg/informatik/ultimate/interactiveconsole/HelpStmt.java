package de.uni_freiburg.informatik.ultimate.interactiveconsole;

/**
 * Statement for outputting help message.
 * 
 * @author Christian Simon
 */
class HelpStmt extends Stmt {
	public HelpStmt () {
	}

	@Override
	public void execute() {
		System.out.println("help                                    - prints these help messages");
		System.out.println("exit                                    - quit Ultimate");
		System.out.println("list                                    - prints index numerated list of available plugins ");
		System.out.println("listmm                                  - prints index numerated list of stored models");
		System.out.println("deletemm <model-index>                  - deletes model with specified index");
		System.out.println("set prelude <filename>                  - sets the prelude to specified file");
		System.out.println("help                                    - prints these help messages");
		System.out.println("use <toolchain> on <boogie filename>    - process specified toolchain on boogie file");
		System.out.println("rerun                                   - reruns the previously selected toolchain on the previously selected file");
		System.out.println("output result to <filename>             - Set the name of the file all results will be written to");
		System.out.println("load preferences from <filename>        - Load stored preferences from a file");
		System.out.println("");
		System.out.println("toolchain ::= current                   - for toolchain currently in use");
		System.out.println("           |  <xml toolchain file>");
		System.out.println("           |  <toolchain description>");
		System.out.println("");
		System.out.println("<toolchain description> ::= plugin index                  <toolchain description>?");
		System.out.println("                         |  ( <toolchain description> )*  <toolchain description>?");
	}
}
