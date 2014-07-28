package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Transform Boolean Term into disjunctive normal form.
 * @author heizmann@informatik.uni-freiburg.de
 */

public class Dnf extends Xnf {
	
	public Dnf(Script script, IUltimateServiceProvider services) {
		super(script, services);
	}
	
	
	@Override
	protected NnfTransformerHelper getNnfTransformerHelper(IUltimateServiceProvider services) {
		return new DnfTransformerHelper(services);
	}



	protected class DnfTransformerHelper extends XnfTransformerHelper {
		
		protected DnfTransformerHelper(IUltimateServiceProvider services) {
			super(services);
		}

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
