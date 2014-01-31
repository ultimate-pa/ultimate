package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.normalForms;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Transform Boolean Term into conjunctive normal form.
 * @author heizmann@informatik.uni-freiburg.de
 */

public class Cnf extends Xnf {
	
	public Cnf(Script script) {
		super(script);
	}
	
	
	@Override
	protected NnfTransformerHelper getNnfTransformerHelper() {
		return new CnfTransformerHelper();
	}



	protected class CnfTransformerHelper extends XnfTransformerHelper {
		
		@Override
		public String innerConnectiveSymbol() {
			return "or";
		}

		@Override
		public String outerConnectiveSymbol() {
			return "and";
		}

		@Override
		public String innerConnectiveNeutralElement() {
			return "false";
		}

		@Override
		public Term innerConnective(Script script, Term... params) {
			Term result = Util.or(m_Script, params);
			return result;
		}

		@Override
		public Term outerConnective(Script script, Term... params) {
			Term result = Util.and(m_Script, params);
			return result;
		}

	}

}
