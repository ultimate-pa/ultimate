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
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.GeometricNonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.AddAxioms;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.CommuHashPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.DNF;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.LassoPartitioneerPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.LassoPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.MatchInOutVars;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RemoveNegation;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteArrays2;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteArraysMapElimination;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteArraysMapElimination.MapEliminationSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteBooleans;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteEquality;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteIte;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteStrictInequalities;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteTrueFalse;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteUserDefinedTypes;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.SimplifyPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.StemAndLoopPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.NonterminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.RankingTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
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
	private final ILogger mLogger;
	private final SimplicationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

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
	private Collection<Lasso> mlassos;

	/**
	 * Global BoogieVars that are modifiable in the procedure where the honda of the lasso lies.
	 */
	private final Set<IProgramVar> mModifiableGlobalsAtHonda;

	/**
	 * SMT script that created the transition formulae
	 */
	protected final Script mOldScript;

	/**
	 * The axioms regarding the transitions' constants
	 */
	protected final Term[] mAxioms;

	/**
	 * The current preferences
	 */
	protected final LassoRankerPreferences mPreferences;

	/**
	 * Set of terms in which RewriteArrays puts additional supporting invariants
	 */
	protected final Set<Term> mArrayIndexSupportingInvariants;

	private final Boogie2SmtSymbolTable mSymbolTable;
	private final ManagedScript mMgdScript;

	private final IUltimateServiceProvider mServices;

	private final IToolchainStorage mStorage;

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

	/**
	 * Constructor for the LassoRanker interface. Calling this invokes the preprocessor on the stem and loop formula.
	 *
	 * If the stem is null, the stem has to be added separately by calling addStem().
	 *
	 * @param script
	 *            the SMT script used to construct the transition formulae
	 * @param boogie2smt
	 *            the boogie2smt object that created the TransFormula's
	 * @param stem
	 *            a transition formula corresponding to the lasso's stem
	 * @param loop
	 *            a transition formula corresponding to the lasso's loop
	 * @param modifiableGlobalsAtHonda
	 *            global BoogieVars that are modifiable in the procedure where the honda of the lasso lies.
	 * @param axioms
	 *            a collection of axioms regarding the transitions' constants
	 * @param preferences
	 *            configuration options for this plugin; these are constant for the life time of this object
	 * @param services
	 * @param storage
	 * @param simplificationTechnique
	 * @param xnfConversionTechnique
	 * @throws TermException
	 *             if preprocessing fails
	 * @throws FileNotFoundException
	 *             if the file for dumping the script cannot be opened
	 */
	public LassoAnalysis(final Script script, final Boogie2SMT boogie2smt,
			final UnmodifiableTransFormula stemTransition, final UnmodifiableTransFormula loopTransition,
			final Set<IProgramVar> modifiableGlobalsAtHonda, final Term[] axioms,
			final LassoRankerPreferences preferences, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final SimplicationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) throws TermException {

		mServices = services;
		mStorage = storage;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mPreferences = new LassoRankerPreferences(preferences); // defensive
																// copy
		mPreferences.checkSanity();
		mLogger.info("Preferences:\n" + mPreferences.toString());

		mOldScript = script;
		mAxioms = axioms;
		mArrayIndexSupportingInvariants = new HashSet<>();
		mMgdScript = boogie2smt.getManagedScript();
		mSymbolTable = boogie2smt.getBoogie2SmtSymbolTable();

		mLassoTerminationAnalysisBenchmarks = new ArrayList<>();

		mLassoNonterminationAnalysisBenchmarks = new ArrayList<>();

		mStemTransition = stemTransition;
		mLoopTransition = loopTransition;
		mModifiableGlobalsAtHonda = modifiableGlobalsAtHonda;
		assert (mLoopTransition != null);

		// Preprocessing creates the Lasso object
		preprocess();

		// This is now a good time to do garbage collection to free the memory
		// allocated during preprocessing. Hopefully it is then available when
		// we call the SMT solver.
	}

	/**
	 * Constructor for the LassoRanker interface. Calling this invokes the preprocessor on the stem and loop formula.
	 *
	 * @param script
	 *            the SMT script used to construct the transition formulae
	 * @param boogie2smt
	 *            the boogie2smt object that created the TransFormulas
	 * @param loop
	 *            a transition formula corresponding to the lasso's loop
	 * @param axioms
	 *            a collection of axioms regarding the transitions' constants
	 * @param preferences
	 *            configuration options for this plugin; these are constant for the life time of this object
	 * @param services
	 * @param storage
	 * @throws TermException
	 *             if preprocessing fails
	 * @throws FileNotFoundException
	 *             if the file for dumping the script cannot be opened
	 */
	public LassoAnalysis(final Script script, final Boogie2SMT boogie2smt, final UnmodifiableTransFormula loop,
			final Set<IProgramVar> modifiableGlobalsAtHonda, final Term[] axioms,
			final LassoRankerPreferences preferences, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final XnfConversionTechnique xnfConversionTechnique,
			final SimplicationTechnique simplificationTechnique) throws TermException, FileNotFoundException {
		this(script, boogie2smt, null, loop, modifiableGlobalsAtHonda, axioms, preferences, services, storage,
				simplificationTechnique, xnfConversionTechnique);
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
		final LassoBuilder lassoBuilder = new LassoBuilder(mLogger, mOldScript, mMgdScript, mStemTransition,
				mLoopTransition, mPreferences.nlaHandling);
		assert lassoBuilder.isSane("initial lasso construction");
		lassoBuilder.preprocess(getPreProcessors(lassoBuilder, mPreferences.overapproximateArrayIndexConnection),
				getPreProcessors(lassoBuilder, false));

		mPreprocessingBenchmark = lassoBuilder.getPreprocessingBenchmark();

		lassoBuilder.constructPolyhedra();

		mlassos = lassoBuilder.getLassos();

		// Some debug messages
		mLogger.debug(new DebugMessage("Original stem:\n{0}", mStemTransition));
		mLogger.debug(new DebugMessage("Original loop:\n{0}", mLoopTransition));
		mLogger.debug(new DebugMessage("After preprocessing:\n{0}", lassoBuilder));
		mLogger.debug("Guesses for Motzkin coefficients: " + eigenvalueGuesses(mlassos));
		mLogger.info("Preprocessing complete.");
	}

	/**
	 * @param lassoBuilder
	 * @return an array of all preprocessors that should be called before termination analysis
	 */
	protected LassoPreprocessor[] getPreProcessors(final LassoBuilder lassoBuilder,
			final boolean overapproximateArrayIndexConnection) {
		final LassoPreprocessor mapElimination;
		if (mPreferences.useOldMapElimination) {
			mapElimination = new RewriteArrays2(true, mStemTransition, mLoopTransition, mModifiableGlobalsAtHonda,
					mServices, mArrayIndexSupportingInvariants, mSymbolTable, mMgdScript,
					lassoBuilder.getReplacementVarFactory(), mSimplificationTechnique, mXnfConversionTechnique);
		} else {
			mapElimination = new RewriteArraysMapElimination(mServices, mMgdScript, mSymbolTable,
					lassoBuilder.getReplacementVarFactory(), mStemTransition, mLoopTransition,
					mModifiableGlobalsAtHonda, mArrayIndexSupportingInvariants,
					new MapEliminationSettings(mSimplificationTechnique, mXnfConversionTechnique));
		}
		return new LassoPreprocessor[] { new StemAndLoopPreprocessor(mOldScript, new MatchInOutVars(mMgdScript)),
				new StemAndLoopPreprocessor(mOldScript,
						new AddAxioms(lassoBuilder.getReplacementVarFactory(), mAxioms)),
				new StemAndLoopPreprocessor(mOldScript, new CommuHashPreprocessor(mServices)),
				mPreferences.enable_partitioneer
						? new LassoPartitioneerPreprocessor(mOldScript, mServices, mMgdScript, mXnfConversionTechnique)
						: null,
				mapElimination, new StemAndLoopPreprocessor(mOldScript, new MatchInOutVars(mMgdScript)),
				mPreferences.enable_partitioneer
						? new LassoPartitioneerPreprocessor(mOldScript, mServices, mMgdScript, mXnfConversionTechnique)
						: null,
				new StemAndLoopPreprocessor(mOldScript, new RewriteDivision(lassoBuilder.getReplacementVarFactory())),
				new StemAndLoopPreprocessor(mOldScript,
						new RewriteBooleans(lassoBuilder.getReplacementVarFactory(), mMgdScript)),
				new StemAndLoopPreprocessor(mOldScript, new RewriteIte(mMgdScript)),
				new StemAndLoopPreprocessor(mOldScript,
						new RewriteUserDefinedTypes(lassoBuilder.getReplacementVarFactory(), mMgdScript)),
				new StemAndLoopPreprocessor(mOldScript, new RewriteEquality()),
				new StemAndLoopPreprocessor(mOldScript, new CommuHashPreprocessor(mServices)),
				new StemAndLoopPreprocessor(mOldScript,
						new SimplifyPreprocessor(mServices, mStorage, mMgdScript, mSimplificationTechnique)),
				new StemAndLoopPreprocessor(mOldScript, new DNF(mServices, mMgdScript, mXnfConversionTechnique)),
				new StemAndLoopPreprocessor(mOldScript,
						new SimplifyPreprocessor(mServices, mStorage, mMgdScript, mSimplificationTechnique)),
				new StemAndLoopPreprocessor(mOldScript, new RewriteTrueFalse()),
				new StemAndLoopPreprocessor(mOldScript, new RemoveNegation()),
				new StemAndLoopPreprocessor(mOldScript, new RewriteStrictInequalities()), };
	}

	/**
	 * @return the preprocessed lassos
	 */
	public Collection<Lasso> getLassos() {
		return mlassos;
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

		final List<GeometricNonTerminationArgument> ntas = new ArrayList<>(mlassos.size());
		if (mlassos.isEmpty()) {
			mlassos.add(new Lasso(LinearTransition.getTranstionTrue(), LinearTransition.getTranstionTrue()));
		}
		for (final Lasso lasso : mlassos) {

			final long startTime = System.nanoTime();
			final NonTerminationArgumentSynthesizer nas =
					new NonTerminationArgumentSynthesizer(lasso, mPreferences, settings, mServices, mStorage);
			final LBool constraintSat = nas.synthesize();
			final long endTime = System.nanoTime();

			final NonterminationAnalysisBenchmark nab =
					new NonterminationAnalysisBenchmark(constraintSat, lasso.getStemVarNum(), lasso.getLoopVarNum(),
							lasso.getStemDisjuncts(), lasso.getLoopDisjuncts(), endTime - startTime);
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

		for (final Lasso lasso : mlassos) {
			// It suffices to prove termination for one component
			final long startTime = System.nanoTime();

			final TerminationArgumentSynthesizer tas = new TerminationArgumentSynthesizer(lasso, template, mPreferences,
					settings, mArrayIndexSupportingInvariants, mServices, mStorage);
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
				final Term[] lexTerm = ta.getRankingFunction().asLexTerm(mOldScript);
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

		public PreprocessingBenchmark(final int intialMaxDagSizeLassos) {
			super();
			mIntialMaxDagSizeLassos = intialMaxDagSizeLassos;
		}

		public void addPreprocessingData(final String description, final int maxDagSizeNontermination,
				final int maxDagSizeLassos) {
			mPreprocessors.add(description);
			mMaxDagSizeLassosAbsolut.add(maxDagSizeLassos);
			mMaxDagSizeLassosRelative
					.add(computeQuotiontOfLastTwoEntries(mMaxDagSizeLassosAbsolut, mIntialMaxDagSizeLassos));
		}

		public void addPreprocessingData(final String description, final int maxDagSizeLassos) {
			mPreprocessors.add(description);
			mMaxDagSizeLassosAbsolut.add(maxDagSizeLassos);
			mMaxDagSizeLassosRelative
					.add(computeQuotiontOfLastTwoEntries(mMaxDagSizeLassosAbsolut, mIntialMaxDagSizeLassos));
		}

		public float computeQuotiontOfLastTwoEntries(final List<Integer> list, final int initialValue) {
			int lastEntry;
			int secondLastEntry;
			if (list.isEmpty()) {
				throw new IllegalArgumentException();
			}
			lastEntry = list.get(list.size() - 1);
			if (list.size() == 1) {
				secondLastEntry = initialValue;
			} else {
				secondLastEntry = list.get(list.size() - 2);
			}
			return ((float) lastEntry) / ((float) secondLastEntry);
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
			final float[] LassosData = new float[preprocessors.size()];
			int LassosAverageInitial = 0;
			for (final PreprocessingBenchmark pb : benchmarks) {
				addListElements(LassosData, pb.getMaxDagSizeLassosRelative());
				LassosAverageInitial += pb.getIntialMaxDagSizeLassos();
			}
			divideAllEntries(LassosData, benchmarks.size());
			LassosAverageInitial /= benchmarks.size();
			final StringBuilder sb = new StringBuilder();
			sb.append("  ");
			sb.append("Lassos: ");
			sb.append("inital");
			sb.append(LassosAverageInitial);
			sb.append(" ");
			sb.append(ppOne(LassosData, preprocessorAbbreviations));
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
			case DNF.s_Description:
				return "dnf";
			case SimplifyPreprocessor.s_Description:
				return "smp";
			case RewriteArrays2.DESCRIPTION:
				return "arr";
			case RewriteEquality.s_Description:
				return "eq";
			case RewriteStrictInequalities.s_Description:
				return "sie";
			case LassoPartitioneerPreprocessor.s_Description:
				return "lsp";
			case RemoveNegation.s_Description:
				return "neg";
			case RewriteDivision.s_Description:
				return "div";
			case RewriteBooleans.s_Description:
				return "bol";
			case MatchInOutVars.s_Description:
				return "mio";
			case RewriteTrueFalse.s_Description:
				return "tf";
			case RewriteIte.s_Description:
				return "ite";
			case AddAxioms.s_Description:
				return "ax";
			case CommuHashPreprocessor.s_Description:
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
			return (int) Math.floor(f * 100);
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
