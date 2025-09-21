/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@outlook.com)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Expression2Term.MultiTermResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IForkActionThreadCurrent.ForkSmtArguments;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IJoinActionThreadCurrent.JoinSmtArguments;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadCurrentTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgJoinThreadCurrentTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Modifies a given {@link IIcfg} by adding copies of existing procedures.
 * <p>
 * Copies are constructed according to the {@link List} argument "instances". For each instance with the name "foo" and
 * the template "bar" we construct a copy of the procedure "foo" such that the identifier of the copy is "bar".
 * </p>
 * <p>
 * A {@link ProcedureMultiplier} copies also all local variables accordingly and replaces the {@link CfgSmtToolkit}.
 * </p>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ProcedureMultiplier {
	private final BasicIcfg<IcfgLocation> mIcfg;
	private final HashRelation<String, String> mCopyDirectives;

	private final ManagedScript mMgdScript;

	private final Set<String> mNewProcedures;
	private final DefaultIcfgSymbolTable mNewSymbolTable;

	// Map from name of procedure duplicate and local variable of original procedure to local variable of duplicate.
	private final Map<String, Map<ILocalProgramVar, ILocalProgramVar>> mLocalVariableMapping;

	// Map from term variable for local variable copy to term variable for original local variable.
	private final Map<Term, Term> mVariableBacktranslationMapping = new HashMap<>();

	// Map from pair of original location and procedure copy name to corresponding location in the procedure copy.
	private final BidirectionalMap<Pair<IcfgLocation, String>, IcfgLocation> mLocationMap = new BidirectionalMap<>();

	// Map from pair of original edge and procedure copy name to corresponding edge in the procedure copy.
	private final BidirectionalMap<Pair<IcfgEdge, String>, IcfgEdge> mEdgeMap = new BidirectionalMap<>();

	private final List<IcfgForkThreadCurrentTransition> mForkCurrentThreads = new ArrayList<>();
	private final List<IcfgJoinThreadCurrentTransition> mJoinCurrentThreads = new ArrayList<>();

	public ProcedureMultiplier(final IUltimateServiceProvider services, final BasicIcfg<IcfgLocation> icfg,
			final List<ThreadInstance> instances) {
		this(services, icfg, generateCopyDirectives(instances));
	}

	public ProcedureMultiplier(final IUltimateServiceProvider services, final BasicIcfg<IcfgLocation> icfg,
			final HashRelation<String, String> copyDirectives) {
		mIcfg = icfg;
		mCopyDirectives = copyDirectives;

		final var originalCsToolkit = icfg.getCfgSmtToolkit();
		mNewProcedures = DataStructureUtils.union(originalCsToolkit.getProcedures(), copyDirectives.projectToRange());
		mNewSymbolTable = new DefaultIcfgSymbolTable(originalCsToolkit.getSymbolTable(), mNewProcedures);

		mMgdScript = icfg.getCfgSmtToolkit().getManagedScript();

		// Add variables
		mLocalVariableMapping = duplicateVariables();

		// Add locations and edges
		for (final String proc : copyDirectives.getDomain()) {
			duplicateProcedureEdges(proc);
		}
	}

	// legacy API used in IcfgPetrifier
	public static void duplicateProcedures(final IUltimateServiceProvider services, final BasicIcfg<IcfgLocation> icfg,
			final List<ThreadInstance> instances, final BlockEncodingBacktranslator backtranslator,
			final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<ThreadInstance>> threadInstanceMap,
			final List<IIcfgForkTransitionThreadCurrent<IcfgLocation>> forkCurrentThreads,
			final List<IIcfgJoinTransitionThreadCurrent<IcfgLocation>> joinCurrentThreads) {
		final var multiplier = new ProcedureMultiplier(services, icfg, instances);
		forkCurrentThreads.addAll(multiplier.mForkCurrentThreads);
		joinCurrentThreads.addAll(multiplier.mJoinCurrentThreads);
		multiplier.updateThreadInstanceMap(threadInstanceMap);
		multiplier.updateBacktranslator(backtranslator);
	}

	// -----------------------------------------------------------------------------------
	// Getters and helpers for translating back and forth between original and duplicates.
	// -----------------------------------------------------------------------------------

	public Map<ILocalProgramVar, ILocalProgramVar> getLocalVariableMapping(final String procedure) {
		return Collections.unmodifiableMap(mLocalVariableMapping.get(procedure));
	}

	public IcfgLocation getOriginalLocation(final IcfgLocation duplicatedLocation) {
		final var pair = mLocationMap.inverse().get(duplicatedLocation);
		if (pair != null) {
			return pair.getFirst();
		}
		return null;
	}

	public IcfgLocation getDuplicatedLocation(final IcfgLocation originalLocation, final String procedureCopy) {
		return mLocationMap.get(new Pair<>(originalLocation, procedureCopy));
	}

	public IcfgEdge getOriginalEdge(final IcfgEdge duplicatedEdge) {
		final var pair = mEdgeMap.inverse().get(duplicatedEdge);
		if (pair != null) {
			return pair.getFirst();
		}
		return null;
	}

	public IcfgEdge getDuplicatedEdge(final IcfgEdge originalEdge, final String procedureCopy) {
		return mEdgeMap.get(new Pair<>(originalEdge, procedureCopy));
	}

	/**
	 * Updates a given backtranslator so that it can backtranslate edges created by the duplication and terms involving
	 * local variables of the procedure copies.
	 *
	 * @param backtranslator
	 *            The backtranslator that shall be updated
	 */
	public void updateBacktranslator(final BlockEncodingBacktranslator backtranslator) {
		backtranslator.setTermTranslator(x -> Substitution.apply(mMgdScript, mVariableBacktranslationMapping, x));
		for (final var entry : mLocationMap.entrySet()) {
			backtranslator.mapLocations(entry.getValue(), entry.getKey().getFirst());
		}
		for (final var entry : mEdgeMap.entrySet()) {
			backtranslator.mapEdges(entry.getValue(), entry.getKey().getFirst());
		}
	}

	public void updateThreadInstanceMap(
			final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<ThreadInstance>> threadInstanceMap) {
		for (final var newForkEdge : mForkCurrentThreads) {
			final var oldForkEdge =
					(IIcfgForkTransitionThreadCurrent<?>) mEdgeMap.inverse().get(newForkEdge).getFirst();
			final List<ThreadInstance> threadInstances = threadInstanceMap.get(oldForkEdge);
			assert threadInstances != null;
			threadInstanceMap.put(newForkEdge, threadInstances);
		}
	}

	// -------------------------------------
	// Actual procedure multiplication code.
	// -------------------------------------

	private void duplicateProcedureEdges(final String proc) {
		final IcfgLocation procEntry = mIcfg.getProcedureEntryNodes().get(proc);
		final List<IcfgEdge> edges =
				new IcfgEdgeIterator(procEntry.getOutgoingEdges()).asStream().collect(Collectors.toList());
		for (final String copyIdentifier : mCopyDirectives.getImage(proc)) {
			final var localVariableMap = getLocalVariableMapping(copyIdentifier);
			for (final IcfgEdge edge : edges) {
				final IcfgLocation source = getOrConstructLocationCopy(edge.getSource(), copyIdentifier);
				final IcfgLocation target = getOrConstructLocationCopy(edge.getTarget(), copyIdentifier);
				final IcfgEdge newEdge = constructEdgeCopy(edge, source, target, localVariableMap);

				final var previousEdge = mEdgeMap.put(new Pair<>(edge, copyIdentifier), newEdge);
				assert previousEdge == null;

				ModelUtils.copyAnnotations(edge, newEdge);
				source.addOutgoing(newEdge);
				target.addIncoming(newEdge);
			}
		}
	}

	private Map<String, Map<ILocalProgramVar, ILocalProgramVar>> duplicateVariables() {
		final Map<String, Map<ILocalProgramVar, ILocalProgramVar>> oldVar2newVar = new HashMap<>();

		final CfgSmtToolkit cfgSmtToolkit = mIcfg.getCfgSmtToolkit();
		final var originalSymbolTable = cfgSmtToolkit.getSymbolTable();
		final Object lockOwner = this;

		final HashRelation<String, IProgramNonOldVar> proc2globals =
				new HashRelation<>(cfgSmtToolkit.getModifiableGlobalsTable().getProcToGlobals());

		final Map<String, List<ILocalProgramVar>> inParams = new HashMap<>(cfgSmtToolkit.getInParams());
		final Map<String, List<ILocalProgramVar>> outParams = new HashMap<>(cfgSmtToolkit.getOutParams());

		mMgdScript.lock(lockOwner);
		for (final String proc : mCopyDirectives.getDomain()) {
			assert cfgSmtToolkit.getProcedures().contains(proc) : "procedure " + proc + " missing";
			for (final String copyIdentifier : mCopyDirectives.getImage(proc)) {
				mIcfg.addProcedure(copyIdentifier);
				final Map<ILocalProgramVar, ILocalProgramVar> procOldVar2NewVar = new HashMap<>();

				final List<ILocalProgramVar> inParamsOfCopy = new ArrayList<>();
				for (final ILocalProgramVar inParam : inParams.get(proc)) {
					final ILocalProgramVar inParamCopy =
							constructVariableCopy(inParam, copyIdentifier, procOldVar2NewVar);
					inParamsOfCopy.add(inParamCopy);
				}
				inParams.put(copyIdentifier, inParamsOfCopy);

				final List<ILocalProgramVar> outParamsOfCopy = new ArrayList<>();
				for (final ILocalProgramVar outParam : outParams.get(proc)) {
					final ILocalProgramVar outParamCopy =
							constructVariableCopy(outParam, copyIdentifier, procOldVar2NewVar);
					outParamsOfCopy.add(outParamCopy);
				}
				outParams.put(copyIdentifier, outParamsOfCopy);

				for (final ILocalProgramVar localVar : originalSymbolTable.getLocals(proc)) {
					if (!procOldVar2NewVar.containsKey(localVar)) {
						constructVariableCopy(localVar, copyIdentifier, procOldVar2NewVar);
					}
				}
				oldVar2newVar.put(copyIdentifier, procOldVar2NewVar);
				proc2globals.getImage(proc).forEach(g -> proc2globals.addPair(copyIdentifier, g));
			}
		}
		mMgdScript.unlock(lockOwner);

		final SmtFunctionsAndAxioms smtSymbols = cfgSmtToolkit.getSmtFunctionsAndAxioms();
		final CfgSmtToolkit newCfgSmtToolkit = new CfgSmtToolkit(new ModifiableGlobalsTable(proc2globals), mMgdScript,
				mNewSymbolTable, mNewProcedures, inParams, outParams, cfgSmtToolkit.getIcfgEdgeFactory(),
				cfgSmtToolkit.getConcurrencyInformation(), smtSymbols);
		mIcfg.setCfgSmtToolkit(newCfgSmtToolkit);

		return oldVar2newVar;
	}

	private IcfgEdge constructEdgeCopy(final IcfgEdge edge, final IcfgLocation source, final IcfgLocation target,
			final Map<ILocalProgramVar, ILocalProgramVar> varReplacement) {
		final UnmodifiableTransFormula transFormula =
				TransFormulaBuilder.constructCopy(mMgdScript, edge.getTransformula(), varReplacement);
		final IcfgEdgeFactory icfgEdgeFactory = mIcfg.getCfgSmtToolkit().getIcfgEdgeFactory();

		if (edge instanceof IcfgInternalTransition) {
			final UnmodifiableTransFormula transFormulaWithBE = TransFormulaBuilder.constructCopy(mMgdScript,
					((IcfgInternalTransition) edge).getTransitionFormulaWithBranchEncoders(), varReplacement);
			return icfgEdgeFactory.createInternalTransition(source, target, null, transFormula, transFormulaWithBE);
		}

		if (edge instanceof IcfgForkThreadCurrentTransition) {
			final IcfgForkThreadCurrentTransition oldForkEdge = (IcfgForkThreadCurrentTransition) edge;
			final ForkSmtArguments newForkSmtArguments =
					copyForkSmtArguments(oldForkEdge.getForkSmtArguments(), varReplacement);
			final IcfgForkThreadCurrentTransition newForkEdge = icfgEdgeFactory.createForkThreadCurrentTransition(
					source, target, null, transFormula, newForkSmtArguments, oldForkEdge.getNameOfForkedProcedure());
			mForkCurrentThreads.add(newForkEdge);
			return newForkEdge;
		}

		if (edge instanceof IcfgJoinThreadCurrentTransition) {
			final JoinSmtArguments newForkSmtArguments = copyJoinSmtArguments(
					((IcfgJoinThreadCurrentTransition) edge).getJoinSmtArguments(), varReplacement);
			final IcfgJoinThreadCurrentTransition newJoinEdge = icfgEdgeFactory
					.createJoinThreadCurrentTransition(source, target, null, transFormula, newForkSmtArguments);
			mJoinCurrentThreads.add(newJoinEdge);
			return newJoinEdge;
		}

		if (edge instanceof IcfgCallTransition) {
			throw new UnsupportedOperationException(String.format(
					"%s does not support %s. Calls and returns should habe been removed by inlining. "
							+ "(Did the inlining fail because this program is recursive?)",
					ProcedureMultiplier.class.getSimpleName(), edge.getClass().getSimpleName()));
		}

		throw new UnsupportedOperationException(
				ProcedureMultiplier.class.getSimpleName() + " does not support " + edge.getClass().getSimpleName());
	}

	private IcfgLocation getOrConstructLocationCopy(final IcfgLocation originalLocation, final String newProc) {
		return mLocationMap.computeIfAbsent(new Pair<>(originalLocation, newProc), this::constructLocationCopy);
	}

	private IcfgLocation constructLocationCopy(final Pair<IcfgLocation, String> originalLocAndNewProc) {
		final var originalLocation = originalLocAndNewProc.getFirst();
		final String originalProc = originalLocation.getProcedure();

		final String newProc = originalLocAndNewProc.getSecond();
		final IcfgLocation newLoc = new IcfgLocation(originalLocation.getDebugIdentifier(), newProc);
		ModelUtils.copyAnnotations(originalLocation, newLoc);

		final boolean isInitial = mIcfg.getInitialNodes().contains(originalLocation);
		final boolean isError = mIcfg.getProcedureErrorNodes().get(originalProc).contains(originalLocation);
		final boolean isProcEntry = mIcfg.getProcedureEntryNodes().get(originalProc).equals(originalLocation);
		final boolean isProcExit = mIcfg.getProcedureExitNodes().get(originalProc).equals(originalLocation);
		final boolean isLoopLocation = mIcfg.getLoopLocations().contains(originalLocation);
		final boolean isLocationOfInterest = mIcfg.getLocationsOfInterest().contains(originalLocation);
		mIcfg.addLocation(newLoc, isInitial, isError, isProcEntry, isProcExit, isLoopLocation, isLocationOfInterest);

		return newLoc;
	}

	private ILocalProgramVar constructVariableCopy(final ILocalProgramVar localVar, final String procedureCopy,
			final Map<ILocalProgramVar, ILocalProgramVar> procOldVar2NewVar) {
		final ILocalProgramVar localVarCopy = ProgramVarUtils.constructLocalProgramVar(localVar.getIdentifier(),
				procedureCopy, localVar.getSort(), mMgdScript, this);
		procOldVar2NewVar.put(localVar, localVarCopy);
		mVariableBacktranslationMapping.put(localVarCopy.getTermVariable(), localVar.getTermVariable());
		mNewSymbolTable.add(localVarCopy);
		return localVarCopy;
	}

	private ForkSmtArguments copyForkSmtArguments(final ForkSmtArguments forkSmtArguments,
			final Map<ILocalProgramVar, ILocalProgramVar> map) {
		final Map<Term, Term> defaultVariableMapping = constructDefaultVariableMapping(map);
		final MultiTermResult newThreadIdArguments =
				copyMultiTermResult(forkSmtArguments.getThreadIdArguments(), defaultVariableMapping);
		final MultiTermResult newProcedureArguments =
				copyMultiTermResult(forkSmtArguments.getProcedureArguments(), defaultVariableMapping);
		return new ForkSmtArguments(newThreadIdArguments, newProcedureArguments);
	}

	private JoinSmtArguments copyJoinSmtArguments(final JoinSmtArguments joinSmtArguments,
			final Map<ILocalProgramVar, ILocalProgramVar> map) {
		final Map<Term, Term> defaultVariableMapping = constructDefaultVariableMapping(map);
		final MultiTermResult newThreadIdArguments =
				copyMultiTermResult(joinSmtArguments.getThreadIdArguments(), defaultVariableMapping);
		final List<IProgramVar> newAssignmentLhs = joinSmtArguments.getAssignmentLhs().stream()
				.map(x -> x.isGlobal() ? x : map.get(x)).collect(Collectors.toList());
		return new JoinSmtArguments(newThreadIdArguments, newAssignmentLhs);
	}

	private MultiTermResult copyMultiTermResult(final MultiTermResult oldProcedureArguments,
			final Map<Term, Term> defaultVariableMapping) {
		final UnaryOperator<Term> subst = (x -> Substitution.apply(mMgdScript, defaultVariableMapping, x));
		final Term[] terms = Arrays.stream(oldProcedureArguments.terms()).map(subst).toArray(Term[]::new);
		final Collection<TermVariable> auxiliaryVars = oldProcedureArguments.auxiliaryVars();
		final Map<String, ILocation> overapproximations = oldProcedureArguments.overapproximations();
		final MultiTermResult copy = new MultiTermResult(overapproximations, auxiliaryVars, terms);
		return copy;
	}

	private static Map<Term, Term> constructDefaultVariableMapping(final Map<ILocalProgramVar, ILocalProgramVar> map) {
		return map.entrySet().stream()
				.collect(Collectors.toMap(x -> x.getKey().getTermVariable(), x -> x.getValue().getTermVariable()));
	}

	private static HashRelation<String, String>
			generateCopyDirectives(final Collection<ThreadInstance> threadInstances) {
		final HashRelation<String, String> result = new HashRelation<>();
		for (final ThreadInstance ti : threadInstances) {
			result.addPair(ti.getThreadTemplateName(), ti.getThreadInstanceName());
		}
		return result;
	}
}
