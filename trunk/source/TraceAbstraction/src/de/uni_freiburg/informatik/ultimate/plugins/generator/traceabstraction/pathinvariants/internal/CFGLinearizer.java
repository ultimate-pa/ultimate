package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;

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

/**
 * Class that contains some code to that demonstrates how TransFormulas
 * can be transformed into LinearTransitions.
 * 
 * The input and the output of this transformation are related as follows.
 * Let the input be a {@link TransFormula} that represents a formula φ whose 
 * free variables are primed and unprimed versions of the {@link BoogieVars} 
 * x_1,...,x_n.
 * The output is a {@link LinearTransition} that represent a formula ψ whose 
 * free variables are primed and unprimed versions of x_1,...,x_n and 
 * additionally primed and unprimed versions of a set 
 * {@link ReplacementVar}s y_1,...,y_m.
 * If we replace for each {@link ReplacementVar} the corresponding primed and 
 * unprimed variables by primed and unprimed versions of the 
 * {@link ReplacementVar}'s definition the the resulting formula is logically 
 * equivalent to the formula φ.
 * 
 * @author Matthias Heizmann
 */
public class CFGLinearizer {
	
	
	private final IUltimateServiceProvider m_Services;
	private final Term[] m_Axioms;
	private final ReplacementVarFactory m_ReplacementVarFactory;
	private final SmtManager m_SmtManager;
	
	public CFGLinearizer(IUltimateServiceProvider services,
			SmtManager smtManager) {
		super();
		m_Services = services;
		m_SmtManager = smtManager;
		m_ReplacementVarFactory = new ReplacementVarFactory(m_SmtManager.getBoogie2Smt().getVariableManager());
		Collection<Term> axioms = m_SmtManager.getBoogie2Smt().getAxioms();
		m_Axioms = axioms.toArray(new Term[axioms.size()]);
		
	}

	private LinearTransition makeLinear(TransFormula tf) {
		TransFormulaLR tflr = TransFormulaLR.buildTransFormula(tf, m_ReplacementVarFactory);

		for (TransitionPreProcessor tpp : getPreprocessors()) {
			try {
				tflr = tpp.process(m_SmtManager.getScript(), tflr);
			} catch (TermException e) {
				throw new RuntimeException(e);
			}
		}
		LinearTransition lt;
		try {
			lt = LinearTransition.fromTransFormulaLR(tflr);
		} catch (TermException e) {
			throw new RuntimeException(e);
		}
		return lt;
	}
	
	private TransitionPreProcessor[] getPreprocessors() {
		return new TransitionPreProcessor[] {
				new MatchInVars(m_SmtManager.getBoogie2Smt().getVariableManager()),
				new AddAxioms(m_Axioms),
				new RewriteDivision(m_ReplacementVarFactory),
				new RewriteBooleans(m_ReplacementVarFactory, m_SmtManager.getScript()),
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
