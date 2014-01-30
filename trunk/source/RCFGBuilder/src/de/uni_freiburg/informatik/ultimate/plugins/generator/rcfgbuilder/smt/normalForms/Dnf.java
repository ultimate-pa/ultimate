package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.normalForms;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.util.Util;

/**
 * Transform Boolean Term into disjunctive normal form.
 * @author heizmann@informatik.uni-freiburg.de
 */

public class Dnf extends Xnf {
	
	public Dnf(Script script) {
		super(script);
	}
	
	
	@Override
	protected NnfTransformerHelper getNnfTransformerHelper() {
		return new DnfTransformerHelper();
	}



	protected class DnfTransformerHelper extends XnfTransformerHelper {
		
		@Override
		public String innerConnectiveSymbol() {
			return "and";
		}

		@Override
		public String outerConnectiveSymbol() {
			return "or";
		}

		@Override
		public String innerConnectiveNeutralElement() {
			return "true";
		}

		@Override
		public Term innerConnective(Script script, Term... params) {
			Term result = Util.and(m_Script, params);
			return result;
		}

		@Override
		public Term outerConnective(Script script, Term... params) {
			Term result = Util.or(m_Script, params);
			return result;
		}

	}

}
