package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.testgeneration;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.SortedMap;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.IcfgProgramExecutionBuilder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedSsaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.RelevantVariables;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class TraceCheckTestGeneration<L extends IAction> extends TraceCheck<L> {

	/**
	 * For now without reuse
	 *
	 * @author Max Barth max.barth@lmu.de
	 */
	public TraceCheckTestGeneration(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts,
			final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> rv, final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final ManagedScript managedScriptTc,
			final AssertCodeBlockOrder assertCodeBlockOrder, final boolean computeRcfgProgramExecution,
			final boolean collectInterpolatSequenceStatistics, final boolean unlockSmtSolverAlsoIfUnsat) {
		super(precondition, postcondition, pendingContexts, rv, services, csToolkit, managedScriptTc,
				assertCodeBlockOrder, computeRcfgProgramExecution, collectInterpolatSequenceStatistics,
				unlockSmtSolverAlsoIfUnsat);
	}

	/**
	 * Compute program execution in the case that the checked specification is violated (result of trace check is SAT).
	 */
	private IcfgProgramExecution<L> computeRcfgProgramExecution(final NestedSsaBuilder<L> nsb) {
		final int vaOrder = -1;
		final RelevantVariables<L> relVars = new RelevantVariables<>(mNestedFormulas,
				mCsToolkit.getModifiableGlobalsTable());
		final IcfgProgramExecutionBuilder<L> rpeb = new IcfgProgramExecutionBuilder<>(
				mCsToolkit.getModifiableGlobalsTable(), mTrace, relVars);
		for (int i = 0; i < mTrace.length(); i++) {
			if (mTrace.getSymbol(i) instanceof IActionWithBranchEncoders) {
				final IActionWithBranchEncoders cb = (IActionWithBranchEncoders) mTrace.getSymbol(i);
				final UnmodifiableTransFormula tf = cb.getTransitionFormulaWithBranchEncoders();
				if (!tf.getBranchEncoders().isEmpty()) {
					final Map<TermVariable, Boolean> beMapping = new HashMap<>();
					for (final TermVariable tv : tf.getBranchEncoders()) {
						final String nameOfConstant = NestedSsaBuilder.branchEncoderConstantName(tv, i);
						final Term indexedBe = mTcSmtManager.getScript().term(nameOfConstant);
						final Term value = super.getValue(indexedBe);
						final Boolean booleanValue = getBooleanValue(value);
						beMapping.put(tv, booleanValue);
					}
					rpeb.setBranchEncoders(i, beMapping);
				}
			}
		}

		final Function<Term, Term> funGetValue;
		if (mCfgManagedScript != mTcSmtManager) {
			funGetValue = a -> new TermTransferrer(mTcSmtManager.getScript(), mCfgManagedScript.getScript())
					.transform(getValue(a));
		} else {
			funGetValue = this::getValue;
		}

		final TestVector testV = extractTestVector(nsb, funGetValue, rpeb, vaOrder);
		final boolean mExportTests = true;
		if (mExportTests) {
			final boolean mExportAllInOneFile = true;
			final String identifier = "" + rpeb.mTrace.hashCode();
			exportTest(testV, identifier, mExportAllInOneFile);
		}

		cleanupAndUnlockSolver();
		return rpeb.getIcfgProgramExecution();
	}

	// does rpeb.addValueAtVarAssignmentPosition and creates a testVector at the same time
	private TestVector extractTestVector(final NestedSsaBuilder<L> nsb, final Function<Term, Term> funGetValue,
			final IcfgProgramExecutionBuilder<L> rpeb, final int vaOrder) {
		final TestVector testV = new TestVector();
		final ArrayList<Term> varAssignment = new ArrayList<>();
		final ArrayList<Pair<Term, Term>> varAssignmentPair = new ArrayList<>();

		for (final var entry : nsb.getIndexedVarRepresentative().entrySet()) {
			final IProgramVar bv = entry.getKey();
			final Map<Integer, Term> indexedRepresentatives = entry.getValue();
			if (SmtUtils.isSortForWhichWeCanGetValues(bv.getTermVariable().getSort())) {
				boolean evenRepresentative = true;
				for (final var representative : indexedRepresentatives.entrySet()) {
					final Integer index = representative.getKey();
					final Term indexedVar = representative.getValue();
					final Term valueT = funGetValue.apply(indexedVar);
					if (indexedVar instanceof ApplicationTerm) {
						assert ((ApplicationTerm) indexedVar).getParameters().length == 0;
						if (indexedVar.toStringDirect().contains("nondet")) {
							if (evenRepresentative) {
								// TODO Not sure if save, but by far the best solution
								if ((index >= 0) && (rpeb.mTrace.asList().get(index) instanceof StatementSequence)) {
									final StatementSequence stsq = (StatementSequence) rpeb.mTrace.asList().get(index);

									final Matcher m = Pattern.compile("__VERIFIER_nondet_(\\w*)")
											.matcher(stsq.getPayload().toString());
									if (m.find()) {
										final String type = m.group(1);
										testV.addValueAssignment(valueT, index, type);
										final TermTransferrer test = new TermTransferrer(mCfgManagedScript.getScript(),
												mTcSmtManager.getScript());
										final Term varEqValue = SmtUtils.binaryEquality(mTcSmtManager.getScript(),
												test.transform(indexedVar), test.transform(valueT));
										final Pair<Term, Term> varValuePair = new Pair<>(test.transform(indexedVar),
												test.transform(valueT));
										varAssignmentPair.add(varValuePair);
										varAssignment.add(varEqValue);
									}
								}
								evenRepresentative = !evenRepresentative;
							} else {
								evenRepresentative = !evenRepresentative;
							}
						}
					}
					rpeb.addValueAtVarAssignmentPosition(bv, index, valueT);

				}
			}
		}
		return testV;
	}

	private void exportTest(final TestVector testV, final String identifier, final boolean allInOneFile) {
		try {
			if (!testV.isEmpty()) {
				mTraceCheckBenchmarkGenerator.reportTestExported();
				TestCaseExporter.getInstance().exportTests(testV, identifier, allInOneFile);
			}
		} catch (final Exception e) {
			// TODO TestGeneration Auto-generated catch block
			e.printStackTrace();
		}
	}
}
