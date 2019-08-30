/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.AddSymbols;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.CommuHashPreprocessor;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.DNF;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.MatchInOutVars;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RemoveNegation;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteBooleans;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteEquality;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteIte;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteStrictInequalities;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteTrueFalse;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteUserDefinedTypes;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.SimplifyPreprocessor;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.GeometricNonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.INonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.LassoPartitioneerPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.LassoPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.MapEliminationLassoPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteArrays2;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.StemAndLoopPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.NonterminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.RankingTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionsAndAxioms;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

/**
 * This is the class that controls LassoRanker's (non-)termination analysis
 *
 * Tools that use LassoRanker as a library probably want to use this class as an interface for invoking LassoRanker.
 * This class can also be derived for a more fine-grained control over the synthesis process.
 *
 * @author Jan Leike
 * @author Matthias Heizmann
 */
public class LassoAnalysis {

	/**
	 * Analysis techniques supported by this library. TODO: Is "analysis techniques" the right term?
	 */
	public enum AnalysisTechnique {
		/**
		 * Termination analysis based on the synthesis of ranking functions and supporting invariants.
		 */
		RANKING_FUNCTIONS_SUPPORTING_INVARIANTS,
		/**
		 * Nontermination analysis based on the synthesis of geometric nontermination arguments.
		 */
		GEOMETRIC_NONTERMINATION_ARGUMENTS,
	}

	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	/**
	 * Stem formula of the linear lasso program
	 */
	private final UnmodifiableTransFormula mStemTransition;

	/**
	 * Loop formula of the linear lasso program
	 */
	private final UnmodifiableTransFormula mLoopTransition;

	/**
	 * Representation of the lasso that we are analyzing which is split into a conjunction of lassos.
	 */
	private Collection<Lasso> mLassos;

	/**
	 * Global BoogieVars that are modifiable in the procedure where the honda of the lasso lies.
	 */
	private final Set<IProgramNonOldVar> mModifiableGlobalsAtHonda;

	/**
	 * The axioms regarding the transitions' constants
	 */
	protected final SmtFunctionsAndAxioms mSmtSymbols;

	/**
	 * The current preferences
	 */
	protected final ILassoRankerPreferences mPreferences;

	/**
	 * Set of terms in which RewriteArrays puts additional supporting invariants
	 */
	protected final Set<Term> mArrayIndexSupportingInvariants;

	private final IIcfgSymbolTable mSymbolTable;
	private final ManagedScript mMgdScript;

	private final IUltimateServiceProvider mServices;

	/**
	 * Benchmark data from last termination analysis. Includes e.g., the number of Motzkin's Theorem applications.
	 */
	private final List<TerminationAnalysisBenchmark> mLassoTerminationAnalysisBenchmarks;

	/**
	 * Benchmark data from last nontermination analysis.
	 */
	private final List<NonterminationAnalysisBenchmark> mLassoNonterminationAnalysisBenchmarks;

	/**
	 * Benchmark data from the preprocessing of the lasso.
	 */
	private PreprocessingBenchmark mPreprocessingBenchmark;
	private final CfgSmtToolkit mCfgSmtToolkit;

	/**
	 * Constructor for the LassoRanker interface. Calling this invokes the preprocessor on the stem and loop formula.
	 *
	 * If the stem is null, the stem has to be added separately by calling addStem().
	 *
	 * @param modifiableGlobalsAtHonda
	 *            global BoogieVars that are modifiable in the procedure where the honda of the lasso lies.
	 * @param smtSymbols
	 *            a collection of smt symbols regarding the transitions' constants
	 * @param preferences
	 *            configuration options for this plugin; these are constant for the life time of this object
	 * @param services
	 * @param simplificationTechnique
	 * @param xnfConversionTechnique
	 * @param script
	 *            the SMT script used to construct the transition formulae
	 * @param boogie2smt
	 *            the boogie2smt object that created the TransFormula's
	 * @param stem
	 *            a transition formula corresponding to the lasso's stem
	 * @param loop
	 *            a transition formula corresponding to the lasso's loop
	 *
	 * @throws TermException
	 *             if preprocessing fails
	 * @throws FileNotFoundException
	 *             if the file for dumping the script cannot be opened
	 */
	public LassoAnalysis(final CfgSmtToolkit csToolkit, final UnmodifiableTransFormula stemTransition,
			final UnmodifiableTransFormula loopTransition, final Set<IProgramNonOldVar> modifiableGlobalsAtHonda,
			final SmtFunctionsAndAxioms smtSymbols, final ILassoRankerPreferences preferences,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) throws TermException {
		mServices = services;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);

		mPreferences = preferences;
		mLogger.info("Preferences:");
		mPreferences.feedSettingsString(mLogger::info);

		mSmtSymbols = smtSymbols;
		mArrayIndexSupportingInvariants = new HashSet<>();
		mMgdScript = csToolkit.getManagedScript();
		mCfgSmtToolkit = csToolkit;
		mSymbolTable = csToolkit.getSymbolTable();

		mLassoTerminationAnalysisBenchmarks = new ArrayList<>();

		mLassoNonterminationAnalysisBenchmarks = new ArrayList<>();

		mStemTransition = stemTransition;
		mLoopTransition = loopTransition;
		mModifiableGlobalsAtHonda = modifiableGlobalsAtHonda;
		assert mLoopTransition != null;

		// Preprocessing creates the Lasso object
		preprocess();

		// This is now a good time to do garbage collection to free the memory
		// allocated during preprocessing. Hopefully it is then available when
		// we call the SMT solver.
	}

	/**
	 * Constructor for the LassoRanker interface. Calling this invokes the preprocessor on the stem and loop formula.
	 * @param loop
	 *            a transition formula corresponding to the lasso's loop
	 * @param symbols
	 *            a collection of axioms regarding the transitions' constants
	 * @param preferences
	 *            configuration options for this plugin; these are constant for the life time of this object
	 * @param services
	 * @param script
	 *            the SMT script used to construct the transition formulae
	 * @param boogie2smt
	 *            the boogie2smt object that created the TransFormulas
	 *
	 * @throws TermException
	 *             if preprocessing fails
	 * @throws FileNotFoundException
	 *             if the file for dumping the script cannot be opened
	 */
	public LassoAnalysis(final CfgSmtToolkit csToolkit, final IIcfgSymbolTable symbolTable,
			final UnmodifiableTransFormula loop, final Set<IProgramNonOldVar> modifiableGlobalsAtHonda,
			final SmtFunctionsAndAxioms symbols, final LassoRankerPreferences preferences, final IUltimateServiceProvider services,
			final XnfConversionTechnique xnfConversionTechnique, final SimplificationTechnique simplificationTechnique) throws TermException, FileNotFoundException {
		this(csToolkit, null, loop, modifiableGlobalsAtHonda, symbols, preferences, services, simplificationTechnique,
				xnfConversionTechnique);
	}

	/**
	 * Preprocess the stem or loop transition. This applies the preprocessor classes and transforms the formula into a
	 * list of inequalities in DNF.
	 *
	 * The list of preprocessors is given by this.getPreProcessors().
	 *
	 * @see PreProcessor
	 * @throws TermException
	 *             if preprocessing fails
	 */
	protected void preprocess() throws TermException {
		mLogger.info("Starting lasso preprocessing...");
		final LassoBuilder lassoBuilder = new LassoBuilder(mLogger, mCfgSmtToolkit, mStemTransition, mLoopTransition,
				mPreferences.getNlaHandling());
		assert lassoBuilder.isSane("initial lasso construction");
		lassoBuilder.preprocess(getPreProcessors(lassoBuilder, mPreferences.isOverapproximateArrayIndexConnection()),
				getPreProcessors(lassoBuilder, false));

		mPreprocessingBenchmark = lassoBuilder.getPreprocessingBenchmark();

		lassoBuilder.constructPolyhedra();

		mLassos = lassoBuilder.getLassos();

		// Some debug messages
		mLogger.debug(new DebugMessage("Original stem:\n{0}", mStemTransition));
		mLogger.debug(new DebugMessage("Original loop:\n{0}", mLoopTransition));
		mLogger.debug(new DebugMessage("After preprocessing:\n{0}", lassoBuilder));
		mLogger.debug("Guesses for Motzkin coefficients: " + eigenvalueGuesses(mLassos));
		mLogger.info("Preprocessing complete.");
	}

	/**
	 * @param lassoBuilder
	 * @return an array of all preprocessors that should be called before termination analysis
	 */
	protected LassoPreprocessor[] getPreProcessors(final LassoBuilder lassoBuilder,
			final boolean overapproximateArrayIndexConnection) {
		final LassoPreprocessor mapElimination;
		if (mPreferences.isUseOldMapElimination()) {
			mapElimination = new RewriteArrays2(true, mStemTransition, mLoopTransition, mModifiableGlobalsAtHonda,
					mServices, mArrayIndexSupportingInvariants, mSymbolTable, mMgdScript,
					lassoBuilder.getReplacementVarFactory(), mSimplificationTechnique, mXnfConversionTechnique);
		} else {
			mapElimination = new MapEliminationLassoPreprocessor(mServices, mMgdScript, mSymbolTable,
					lassoBuilder.getReplacementVarFactory(), mStemTransition, mLoopTransition,
					mModifiableGlobalsAtHonda, mArrayIndexSupportingInvariants,
					mPreferences.getMapEliminationSettings(mSimplificationTechnique, mXnfConversionTechnique));
		}
		return new LassoPreprocessor[] { new StemAndLoopPreprocessor(mMgdScript, new MatchInOutVars()),
				new StemAndLoopPreprocessor(mMgdScript,
						new AddSymbols(lassoBuilder.getReplacementVarFactory(), mSmtSymbols)),
				new StemAndLoopPreprocessor(mMgdScript, new CommuHashPreprocessor(mServices)),
				mPreferences.isEnablePartitioneer()
						? new LassoPartitioneerPreprocessor(mMgdScript, mServices, mXnfConversionTechnique)
						: null,
				mapElimination, new StemAndLoopPreprocessor(mMgdScript, new MatchInOutVars()),
				mPreferences.isEnablePartitioneer()
						? new LassoPartitioneerPreprocessor(mMgdScript, mServices, mXnfConversionTechnique)
						: null,
				new StemAndLoopPreprocessor(mMgdScript, new RewriteDivision(lassoBuilder.getReplacementVarFactory())),
				new StemAndLoopPreprocessor(mMgdScript,
						new RewriteBooleans(lassoBuilder.getReplacementVarFactory(), mMgdScript)),
				new StemAndLoopPreprocessor(mMgdScript, new RewriteIte()),
				new StemAndLoopPreprocessor(mMgdScript,
						new RewriteUserDefinedTypes(lassoBuilder.getReplacementVarFactory(), mMgdScript)),
				new StemAndLoopPreprocessor(mMgdScript, new RewriteEquality()),
				new StemAndLoopPreprocessor(mMgdScript, new CommuHashPreprocessor(mServices)),
				new StemAndLoopPreprocessor(mMgdScript,
						new SimplifyPreprocessor(mServices, mSimplificationTechnique)),
				new StemAndLoopPreprocessor(mMgdScript, new DNF(mServices, mXnfConversionTechnique)),
				new StemAndLoopPreprocessor(mMgdScript,
						new SimplifyPreprocessor(mServices, mSimplificationTechnique)),
				new StemAndLoopPreprocessor(mMgdScript, new RewriteTrueFalse()),
				new StemAndLoopPreprocessor(mMgdScript, new RemoveNegation()),
				new StemAndLoopPreprocessor(mMgdScript, new RewriteStrictInequalities()), };
	}

	/**
	 * @return the preprocessed lassos
	 */
	public Collection<Lasso> getLassos() {
		return mLassos;
	}

	public List<TerminationAnalysisBenchmark> getTerminationAnalysisBenchmarks() {
		return mLassoTerminationAnalysisBenchmarks;
	}

	public List<NonterminationAnalysisBenchmark> getNonterminationAnalysisBenchmarks() {
		return mLassoNonterminationAnalysisBenchmarks;
	}

	public PreprocessingBenchmark getPreprocessingBenchmark() {
		return mPreprocessingBenchmark;
	}

	protected String benchmarkScriptMessage(final LBool constraintSat, final RankingTemplate template) {
		final StringBuilder sb = new StringBuilder();
		sb.append("BenchmarkResult: ");
		sb.append(constraintSat);
		sb.append(" for template ");
		sb.append(template.getName());
		sb.append(" with degree ");
		sb.append(template.getDegree());
		sb.append(". ");
		sb.append(mLassoTerminationAnalysisBenchmarks.toString());
		return sb.toString();
	}

	/**
	 * @return a pretty version of the guesses for loop eigenvalues
	 */
	protected static String eigenvalueGuesses(final Collection<Lasso> lassos) {
		final StringBuilder sb = new StringBuilder();
		sb.append("[");
		for (final Lasso lasso : lassos) {
			final Rational[] eigenvalues = lasso.guessEigenvalues(true);
			for (int i = 0; i < eigenvalues.length; ++i) {
				if (i > 0) {
					sb.append(", ");
				}
				sb.append(eigenvalues[i].toString());
			}
		}
		sb.append("]");
		return sb.toString();
	}

	/**
	 * Try to find a non-termination argument for the lasso program.
	 *
	 * @param settings
	 *            (local) settings for nontermination analysis
	 * @param services
	 * @return the list of non-termination arguments (one for each component) or null if at least one component does not
	 *         have one
	 * @throws IOException
	 */
	public GeometricNonTerminationArgument checkNonTermination(final NonTerminationAnalysisSettings settings)
			throws SMTLIBException, TermException, IOException {
		mLogger.info("Checking for nontermination...");

		final List<GeometricNonTerminationArgument> ntas = new ArrayList<>(mLassos.size());
		if (mLassos.isEmpty()) {
			mLassos.add(new Lasso(LinearTransition.getTranstionTrue(), LinearTransition.getTranstionTrue()));
		}
		for (final Lasso lasso : mLassos) {

			final long startTime = System.nanoTime();
			final NonTerminationAnalysisSettings gev0settings = constructGev0Copy(settings);
			NonTerminationArgumentSynthesizer nas =
					new NonTerminationArgumentSynthesizer(lasso, mPreferences, gev0settings, mServices);
			LBool constraintSat = nas.synthesize();
			if (constraintSat == LBool.UNSAT) {
				nas.close();
				nas = new NonTerminationArgumentSynthesizer(lasso, mPreferences, settings, mServices);
				constraintSat = nas.synthesize();
			}

			final long endTime = System.nanoTime();

			final boolean isFixpoint;
			if (constraintSat == LBool.SAT) {
				isFixpoint = nas.getArgument().getLambdas().isEmpty() || nas.getArgument().getGEVs().isEmpty();
			} else {
				isFixpoint = false;
			}
			final NonterminationAnalysisBenchmark nab = new NonterminationAnalysisBenchmark(constraintSat, isFixpoint,
					lasso.getStemVarNum(), lasso.getLoopVarNum(), lasso.getStemDisjuncts(), lasso.getLoopDisjuncts(),
					endTime - startTime);
			mLassoNonterminationAnalysisBenchmarks.add(nab);

			if (constraintSat == LBool.SAT) {
				mLogger.info("Proved nontermination for one component.");
				final GeometricNonTerminationArgument nta = nas.getArgument();
				ntas.add(nta);
				mLogger.info(nta);
			} else if (constraintSat == LBool.UNKNOWN) {
				mLogger.info("Proving nontermination failed: SMT Solver returned 'unknown'.");
			} else if (constraintSat == LBool.UNSAT) {
				mLogger.info("Proving nontermination failed: No geometric nontermination argument exists.");
			} else {
				assert false;
			}
			nas.close();
			if (constraintSat != LBool.SAT) {
				// One component did not have a nontermination argument.
				// Therefore we have to give up.
				return null;
			}
		}

		// Join nontermination arguments
		assert !ntas.isEmpty();
		GeometricNonTerminationArgument nta = ntas.get(0);
		for (int i = 1; i < ntas.size(); ++i) {
			nta = nta.join(ntas.get(i));
		}
		return nta;
	}

	private NonTerminationAnalysisSettings constructGev0Copy(final INonTerminationAnalysisSettings settings) {
		return new NonTerminationAnalysisSettings(new NonTerminationAnalysisSettings(settings) {

			@Override
			public int getNumberOfGevs() {
				return 0;
			}

		});
	}

	/**
	 * Try to find a termination argument for the lasso program specified by the given ranking function template.
	 *
	 * @param template
	 *            the ranking function template
	 * @param settings
	 *            (local) settings for termination analysis
	 * @return the termination argument or null of none is found
	 * @throws IOException
	 */
	public TerminationArgument tryTemplate(final RankingTemplate template, final TerminationAnalysisSettings settings)
			throws SMTLIBException, TermException, IOException {
		// ignore stem
		mLogger.info("Using template '" + template.getName() + "'.");
		mLogger.debug(template);

		for (final Lasso lasso : mLassos) {
			// It suffices to prove termination for one component
			final long startTime = System.nanoTime();

			final TerminationArgumentSynthesizer tas = new TerminationArgumentSynthesizer(lasso, template, mPreferences,
					settings, mArrayIndexSupportingInvariants, mServices);
			final LBool constraintSat = tas.synthesize();

			final long endTime = System.nanoTime();

			final TerminationAnalysisBenchmark tab =
					new TerminationAnalysisBenchmark(constraintSat, lasso.getStemVarNum(), lasso.getLoopVarNum(),
							lasso.getStemDisjuncts(), lasso.getLoopDisjuncts(), template.getName(),
							template.getDegree(), tas.getNumSIs(), tas.getNumMotzkin(), endTime - startTime);
			mLassoTerminationAnalysisBenchmarks.add(tab);
			mLogger.debug(benchmarkScriptMessage(constraintSat, template));

			if (constraintSat == LBool.SAT) {
				mLogger.info("Proved termination.");
				final TerminationArgument ta = tas.getArgument();
				mLogger.info(ta);
				final Term[] lexTerm = ta.getRankingFunction().asLexTerm(mMgdScript.getScript());
				for (final Term t : lexTerm) {
					mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t)));
				}
				tas.close();
				return ta;
			} else if (constraintSat == LBool.UNKNOWN) {
				mLogger.info("Proving termination failed: SMT Solver returned 'unknown'.");
			} else if (constraintSat == LBool.UNSAT) {
				mLogger.info("Proving termination failed for this template and these settings.");
			} else {
				assert false;
			}
			tas.close();
		}
		// No lasso hat a termination argument, so we have to give up
		return null;
	}

	/**
	 * Objects for collecting data from the preprocessing steps.
	 *
	 * @author Matthias Heizmann
	 *
	 */
	public static class PreprocessingBenchmark {
		private final int mIntialMaxDagSizeLassos;
		private final List<String> mPreprocessors = new ArrayList<>();
		private final List<Integer> mMaxDagSizeLassosAbsolut = new ArrayList<>();
		private final List<Float> mMaxDagSizeLassosRelative = new ArrayList<>();

		public PreprocessingBenchmark(final long l) {
			super();
			mIntialMaxDagSizeLassos = Math.toIntExact(l);
		}

		public void addPreprocessingData(final String description, final int maxDagSizeNontermination,
				final int maxDagSizeLassos) {
			mPreprocessors.add(description);
			mMaxDagSizeLassosAbsolut.add(maxDagSizeLassos);
			mMaxDagSizeLassosRelative
					.add(computeQuotiontOfLastTwoEntries(mMaxDagSizeLassosAbsolut, mIntialMaxDagSizeLassos));
		}

		public void addPreprocessingData(final String description, final long l) {
			mPreprocessors.add(description);
			mMaxDagSizeLassosAbsolut.add(Math.toIntExact(l));
			mMaxDagSizeLassosRelative
					.add(computeQuotiontOfLastTwoEntries(mMaxDagSizeLassosAbsolut, mIntialMaxDagSizeLassos));
		}

		public float computeQuotiontOfLastTwoEntries(final List<Integer> list, final int initialValue) {
			if (list.isEmpty()) {
				throw new IllegalArgumentException();
			}
			final double secondLastEntry;
			final double lastEntry = list.get(list.size() - 1);
			if (list.size() == 1) {
				secondLastEntry = initialValue;
			} else {
				secondLastEntry = list.get(list.size() - 2);
			}
			return (float) (lastEntry / secondLastEntry);
		}

		public int getIntialMaxDagSizeLassos() {
			return mIntialMaxDagSizeLassos;
		}

		public List<String> getPreprocessors() {
			return mPreprocessors;
		}

		public List<String> getPreprocessorsNon() {
			return mPreprocessors;
		}

		public List<Float> getMaxDagSizeLassosRelative() {
			return mMaxDagSizeLassosRelative;
		}

		public static String prettyprint(final List<PreprocessingBenchmark> benchmarks) {
			if (benchmarks.isEmpty()) {
				return "";
			}
			final List<String> preprocessors = benchmarks.get(0).getPreprocessors();
			final List<String> preprocessorAbbreviations = computeAbbrev(preprocessors);
			final float[] lassosData = new float[preprocessors.size()];
			int lassosAverageInitial = 0;
			for (final PreprocessingBenchmark pb : benchmarks) {
				addListElements(lassosData, pb.getMaxDagSizeLassosRelative());
				lassosAverageInitial += pb.getIntialMaxDagSizeLassos();
			}
			divideAllEntries(lassosData, benchmarks.size());
			lassosAverageInitial /= benchmarks.size();
			final StringBuilder sb = new StringBuilder();
			sb.append("  ");
			sb.append("Lassos: ");
			sb.append("inital");
			sb.append(lassosAverageInitial);
			sb.append(" ");
			sb.append(ppOne(lassosData, preprocessorAbbreviations));
			return sb.toString();
		}

		private static List<String> computeAbbrev(final List<String> preprocessors) {
			final List<String> result = new ArrayList<>();
			for (final String description : preprocessors) {
				result.add(computeAbbrev(description));
			}
			return result;
		}

		private static String computeAbbrev(final String ppId) {
			switch (ppId) {
			case DNF.DESCRIPTION:
				return "dnf";
			case SimplifyPreprocessor.DESCRIPTION:
				return "smp";
			case RewriteArrays2.DESCRIPTION:
				return "arr";
			case RewriteEquality.DESCRIPTION:
				return "eq";
			case RewriteStrictInequalities.DESCRIPTION:
				return "sie";
			case LassoPartitioneerPreprocessor.s_Description:
				return "lsp";
			case RemoveNegation.DESCRIPTION:
				return "neg";
			case RewriteDivision.DESCRIPTION:
				return "div";
			case RewriteBooleans.DESCRIPTION:
				return "bol";
			case MatchInOutVars.DESCRIPTION:
				return "mio";
			case RewriteTrueFalse.DESCRIPTION:
				return "tf";
			case RewriteIte.DESCRIPTION:
				return "ite";
			case AddSymbols.DESCRIPTION:
				return "ax";
			case CommuHashPreprocessor.DESCRIPTION:
				return "hnf";
			default:
				return "ukn";
			}
		}

		private static String ppOne(final float[] relativeEqualizedData, final List<String> preprocessorAbbreviations) {
			final StringBuilder sb = new StringBuilder();
			for (int i = 0; i < relativeEqualizedData.length; i++) {
				sb.append(preprocessorAbbreviations.get(i));
				sb.append(String.valueOf(makePercent(relativeEqualizedData[i])));
				sb.append(" ");
			}
			return sb.toString();
		}

		private static int makePercent(final float f) {
			return (int) Math.floor(f * 100.0);
		}

		private static void addListElements(final float[] modifiedArray, final List<Float> incrementList) {
			assert modifiedArray.length == incrementList.size();
			for (int i = 0; i < modifiedArray.length; i++) {
				modifiedArray[i] += incrementList.get(i);
			}
		}

		private static void divideAllEntries(final float[] modifiedArray, final int divisor) {
			for (int i = 0; i < modifiedArray.length; i++) {
				modifiedArray[i] /= divisor;
			}
		}

	}
}
