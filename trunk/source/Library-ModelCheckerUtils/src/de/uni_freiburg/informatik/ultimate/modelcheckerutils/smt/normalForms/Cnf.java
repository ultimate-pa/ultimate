package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

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
		public String innerJunctionName() {
			return "disjunction";
		}

		@Override
		public String outerJunctionName() {
			return "conjuction";
		}

		@Override
		public Term innerConnective(Script script, List<Term> params) {
			Term result = SmtUtils.or(m_Script, params);
			return result;
		}

		@Override
		public Term outerConnective(Script script, List<Term> params) {
			Term result = SmtUtils.and(m_Script, params);
			return result;
		}

		@Override
		public Term[] getOuterJuncts(Term term) {
			return SmtUtils.getConjuncts(term);
		}

	}

}
