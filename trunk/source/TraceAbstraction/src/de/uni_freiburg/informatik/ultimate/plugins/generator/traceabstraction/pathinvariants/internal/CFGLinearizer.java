package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.AddAxioms;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.DNF;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.MatchInVars;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RemoveNegation;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteBooleans;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteEquality;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteIte;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteStrictInequalities;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteTrueFalse;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.SimplifyPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.TransitionPreProcessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class CFGLinearizer {
	
	
	private Term[] m_axioms;
	private ReplacementVarFactory replacementVarFactory;
	private SmtManager m_SmtManager;
	private IUltimateServiceProvider m_Services;

	private LinearTransition makeLinear(TransFormula tf) {
		TransFormulaLR tflr = TransFormulaLR.buildTransFormula(tf, replacementVarFactory);

		for (TransitionPreProcessor tpp : getPreprocessors()) {
			try {
				tflr = tpp.process(m_SmtManager.getScript(), tflr);
			} catch (TermException e) {
				throw new RuntimeException();
			}
		}
		LinearTransition lt;
		try {
			lt = LinearTransition.fromTransFormulaLR(tflr);
		} catch (TermException e) {
			throw new AssertionError();
		}
		return lt;
	}
	
	private TransitionPreProcessor[] getPreprocessors() {
		return new TransitionPreProcessor[] {
				new MatchInVars(m_SmtManager.getBoogie2Smt().getVariableManager()),
				new AddAxioms(m_axioms),
				new RewriteDivision(replacementVarFactory),
				new RewriteBooleans(replacementVarFactory, m_SmtManager.getScript()),
				new RewriteIte(),
				new RewriteEquality(),
				new SimplifyPreprocessor(m_Services),
				new DNF(m_Services),
				new SimplifyPreprocessor(m_Services),
				new RewriteTrueFalse(),
				new RemoveNegation(),
				new RewriteStrictInequalities(),
		};
	}

}
