package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents all commands that take one term.  These are
 * - assert
 * - simplify
 * @author Juergen Christ
 */
public class OneTermCmd extends AbstractOneTermCmd {
	
	private String m_Cmd;
	
	public OneTermCmd(String cmd, Term term) {
		super(term);
		m_Cmd = cmd;
	}

	@Override
	public void dump(PrintWriter out) {
		super.dump(out);
		out.print('(');
		out.print(m_Cmd);
		out.print(' ');
		new PrintTerm().append(out, m_Term);
		out.println(')');
	}
	
	public String getCmd() {
		return m_Cmd;
	}
	
	@Override
	public void insertDefinitions(Map<String, Cmd> context) {
		new NamedHelper().addNames(m_Term, context, this);
	}

	@Override
	public void addUsedDefinitions(Map<String, Cmd> context, Set<Cmd> usedDefs) {
		new DefinitionTracker(context, usedDefs).track(m_Term);
	}
	
	public String toString() {
		return m_Cmd.toUpperCase();
	}

}
