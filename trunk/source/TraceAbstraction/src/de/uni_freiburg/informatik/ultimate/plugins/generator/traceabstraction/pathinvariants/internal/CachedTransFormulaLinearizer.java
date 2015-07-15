package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

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
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteUserDefinedTypes;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.SimplifyPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.TransitionPreProcessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * Class linearizing {@link TransFormula}s. For improved performance and
 * variable management, this class keeps a cache of linearization results. Thus,
 * this class should only be used in one single context at a time, to ensure
 * proper garbage collection.
 * 
 * @author (mostly) Matthias Heizmann
 */
public class CachedTransFormulaLinearizer {

	private final IUltimateServiceProvider m_Services;
	private final Term[] m_Axioms;
	private final ReplacementVarFactory m_ReplacementVarFactory;
	private final SmtManager m_SmtManager;
	private final Map<TransFormula, LinearTransition> m_Cache;

	/**
	 * Constructs a cached TransFormula linearizer.
	 * 
	 * @param services
	 *            Service provider to use
	 * @param smtManager
	 *            SMT manager
	 * @author Matthias Heizmann
	 */
	public CachedTransFormulaLinearizer(IUltimateServiceProvider services,
			SmtManager smtManager) {
		super();
		m_Services = services;
		m_SmtManager = smtManager;
		m_ReplacementVarFactory = new ReplacementVarFactory(m_SmtManager
				.getBoogie2Smt().getVariableManager());
		Collection<Term> axioms = m_SmtManager.getBoogie2Smt().getAxioms();
		m_Axioms = axioms.toArray(new Term[axioms.size()]);

		m_Cache = new HashMap<TransFormula, LinearTransition>();
	}

	/**
	 * Performs a transformation, utilizing the cache if possible. If the given
	 * {@link TransFormula} has not yet been linearized, the result will also
	 * get added to the cache.
	 * 
	 * The input and the output of this transformation are related as follows.
	 * Let the input be a {@link TransFormula} that represents a formula φ whose
	 * free variables are primed and unprimed versions of the {@link BoogieVars}
	 * x_1,...,x_n. The output is a {@link LinearTransition} that represent a
	 * formula ψ whose free variables are primed and unprimed versions of
	 * x_1,...,x_n and additionally primed and unprimed versions of a set
	 * {@link ReplacementVar}s y_1,...,y_m. If we replace for each
	 * {@link ReplacementVar} the corresponding primed and unprimed variables by
	 * primed and unprimed versions of the {@link ReplacementVar}'s definition
	 * the the resulting formula is logically equivalent to the formula φ.
	 * 
	 * @param tf
	 *            transformula to transform
	 * @return transformed transformula
	 */
	public LinearTransition linearize(final TransFormula tf) {
		LinearTransition result = m_Cache.get(tf);
		if (result == null) {
			result = makeLinear(tf);
			m_Cache.put(tf, result);
		}
		return result;
	}

	/**
	 * Performs a transformation.
	 * 
	 * The input and the output of this transformation are related as follows.
	 * Let the input be a {@link TransFormula} that represents a formula φ whose
	 * free variables are primed and unprimed versions of the {@link BoogieVars}
	 * x_1,...,x_n. The output is a {@link LinearTransition} that represent a
	 * formula ψ whose free variables are primed and unprimed versions of
	 * x_1,...,x_n and additionally primed and unprimed versions of a set
	 * {@link ReplacementVar}s y_1,...,y_m. If we replace for each
	 * {@link ReplacementVar} the corresponding primed and unprimed variables by
	 * primed and unprimed versions of the {@link ReplacementVar}'s definition
	 * the the resulting formula is logically equivalent to the formula φ.
	 * 
	 * @author Matthias Heizmann
	 * @param tf
	 *            transformula to transform
	 * @return transformed transformula
	 */
	private LinearTransition makeLinear(TransFormula tf) {
		TransFormulaLR tflr = TransFormulaLR.buildTransFormula(tf,
				m_ReplacementVarFactory);

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

	/**
	 * (Undocumented Method, do not touch)
	 * 
	 * @author Matthias Heizmann
	 */
	private TransitionPreProcessor[] getPreprocessors() {
		return new TransitionPreProcessor[] {
				new MatchInVars(m_SmtManager.getBoogie2Smt().getVariableManager()),
				new AddAxioms(m_Axioms),
				new RewriteDivision(m_ReplacementVarFactory),
				new RewriteBooleans(m_ReplacementVarFactory, m_SmtManager.getScript()), 
				new RewriteIte(),
				new RewriteUserDefinedTypes(m_ReplacementVarFactory, m_SmtManager.getScript()),
				new RewriteEquality(), 
				new SimplifyPreprocessor(m_Services),
				new DNF(m_Services, m_SmtManager.getVariableManager()), 
				new SimplifyPreprocessor(m_Services),
				new RewriteTrueFalse(), 
				new RemoveNegation(),
				new RewriteStrictInequalities(), };
	}

}
