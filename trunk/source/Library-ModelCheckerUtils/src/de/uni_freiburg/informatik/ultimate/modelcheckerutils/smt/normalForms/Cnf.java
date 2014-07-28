package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Transform Boolean Term into conjunctive normal form.
 * @author heizmann@informatik.uni-freiburg.de
 */

public class Cnf extends Xnf {
	
	public Cnf(Script script, IUltimateServiceProvider services) {
		super(script,services);
	}
	
	
	@Override
	protected NnfTransformerHelper getNnfTransformerHelper(IUltimateServiceProvider services) {
		return new CnfTransformerHelper(services);
	}



	protected class CnfTransformerHelper extends XnfTransformerHelper {
		
		protected CnfTransformerHelper(IUltimateServiceProvider services) {
			super(services);
		}

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
