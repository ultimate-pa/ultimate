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
import java.util.HashMap;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Modifies a given {@link IIcfg} by adding copies of existing procedures.
 * <p>
 * Copies are constructed according to the {@link List} argument "instances". For each instance with the name "foo" and
 * the template "bar" we construct a copy of the procedure "foo" and the identifier of the copy is "bar".
 * <p />
 * <p>
 * A {@link ProcedureMultiplier} replaces also all local variables accordingly and replaces the {@link CfgSmtToolkit}.
 * <p />
 * <p>
 * For every copy e_copy of an edge e, the map entry (e_copy,e) is added to the given
 * {@link BlockEncodingBacktranslator}.
 * <p />
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class ProcedureMultiplier {
	public static void duplicateProcedures(final IUltimateServiceProvider services, final BasicIcfg<IcfgLocation> icfg,
			final List<ThreadInstance> instances, final BlockEncodingBacktranslator backtranslator,
			final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<ThreadInstance>> threadInstanceMap,
			final List<IIcfgForkTransitionThreadCurrent<IcfgLocation>> forkCurrentThreads,
			final List<IIcfgJoinTransitionThreadCurrent<IcfgLocation>> joinCurrentThreads) {
		final Object lockOwner = ProcedureMultiplier.class;
		final HashRelation<String, String> copyDirectives = generateCopyDirectives(instances);
		final CfgSmtToolkit cfgSmtToolkit = icfg.getCfgSmtToolkit();
		final IcfgEdgeFactory icfgEdgeFactory = cfgSmtToolkit.getIcfgEdgeFactory();
		final Map<String, List<ILocalProgramVar>> inParams = new HashMap<>(cfgSmtToolkit.getInParams());
		final Map<String, List<ILocalProgramVar>> outParams = new HashMap<>(cfgSmtToolkit.getOutParams());
		final Set<String> procedures = new HashSet<>(cfgSmtToolkit.getProcedures());
		final SmtFunctionsAndAxioms smtSymbols = cfgSmtToolkit.getSmtFunctionsAndAxioms();
		final DefaultIcfgSymbolTable symbolTable =
				new DefaultIcfgSymbolTable(cfgSmtToolkit.getSymbolTable(), procedures);
		final ManagedScript managedScript = cfgSmtToolkit.getManagedScript();
		final HashRelation<String, IProgramNonOldVar> proc2globals =
				new HashRelation<>(cfgSmtToolkit.getModifiableGlobalsTable().getProcToGlobals());

		// Add variables
		final Map<String, Map<ILocalProgramVar, ILocalProgramVar>> oldVar2newVar = new HashMap<>();
		final Map<Term, Term> variableBacktranslationMapping = new HashMap<>();
		managedScript.lock(lockOwner);
		for (final String proc : copyDirectives.getDomain()) {
			assert cfgSmtToolkit.getProcedures().contains(proc) : "procedure " + proc + " missing";
			for (final String copyIdentifier : copyDirectives.getImage(proc)) {
				icfg.addProcedure(copyIdentifier);
				final Map<ILocalProgramVar, ILocalProgramVar> procOldVar2NewVar = new HashMap<>();
				procedures.add(copyIdentifier);
				final List<ILocalProgramVar> inParamsOfCopy = new ArrayList<>();
				for (final ILocalProgramVar inParam : inParams.get(proc)) {
					final ILocalProgramVar inParamCopy = constructVariableCopy(inParam, copyIdentifier, managedScript,
							procOldVar2NewVar, variableBacktranslationMapping, symbolTable, lockOwner);
					inParamsOfCopy.add(inParamCopy);
				}
				inParams.put(copyIdentifier, inParamsOfCopy);
				final List<ILocalProgramVar> outParamsOfCopy = new ArrayList<>();
				for (final ILocalProgramVar outParam : outParams.get(proc)) {
					final ILocalProgramVar outParamCopy = constructVariableCopy(outParam, copyIdentifier, managedScript,
							procOldVar2NewVar, variableBacktranslationMapping, symbolTable, lockOwner);
					outParamsOfCopy.add(outParamCopy);
				}
				outParams.put(copyIdentifier, outParamsOfCopy);
				for (final ILocalProgramVar localVar : cfgSmtToolkit.getSymbolTable().getLocals(proc)) {
					if (!procOldVar2NewVar.containsKey(localVar)) {
						constructVariableCopy(localVar, copyIdentifier, managedScript, procOldVar2NewVar,
								variableBacktranslationMapping, symbolTable, lockOwner);
					}
				}
				oldVar2newVar.put(copyIdentifier, procOldVar2NewVar);
				proc2globals.getImage(proc).forEach(g -> proc2globals.addPair(copyIdentifier, g));
			}
		}
		backtranslator.setTermTranslator(x -> Substitution.apply(managedScript, variableBacktranslationMapping, x));
		managedScript.unlock(lockOwner);

		final CfgSmtToolkit newCfgSmtToolkit =
				new CfgSmtToolkit(new ModifiableGlobalsTable(proc2globals), managedScript, symbolTable, procedures,
						inParams, outParams, icfgEdgeFactory, cfgSmtToolkit.getConcurrencyInformation(), smtSymbols);
		icfg.setCfgSmtToolkit(newCfgSmtToolkit);

		// Add locations and edges
		for (final String proc : copyDirectives.getDomain()) {
			final IcfgLocation procEntry = icfg.getProcedureEntryNodes().get(proc);
			final List<IcfgEdge> edges =
					new IcfgEdgeIterator(procEntry.getOutgoingEdges()).asStream().collect(Collectors.toList());
			for (final String copyIdentifier : copyDirectives.getImage(proc)) {
				final Map<IcfgLocation, IcfgLocation> old2NewLoc = new HashMap<>();
				for (final IcfgEdge edge : edges) {
					final IcfgLocation source = getOrConstructLocationCopy(edge.getSource(), old2NewLoc, icfg,
							copyIdentifier, backtranslator);
					final IcfgLocation target = getOrConstructLocationCopy(edge.getTarget(), old2NewLoc, icfg,
							copyIdentifier, backtranslator);
					final IcfgEdge newEdge = constructEdgeCopy(edge, source, target, oldVar2newVar.get(copyIdentifier),
							icfgEdgeFactory, managedScript, threadInstanceMap, forkCurrentThreads, joinCurrentThreads);
					backtranslator.mapEdges(newEdge, edge);
					ModelUtils.copyAnnotations(edge, newEdge);
					source.addOutgoing(newEdge);
					target.addIncoming(newEdge);
				}
			}
		}
	}

	private static IcfgEdge constructEdgeCopy(final IcfgEdge edge, final IcfgLocation source, final IcfgLocation target,
			final Map<ILocalProgramVar, ILocalProgramVar> varReplacement, final IcfgEdgeFactory icfgEdgeFactory,
			final ManagedScript managedScript,
			final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<ThreadInstance>> threadInstanceMap,
			final List<IIcfgForkTransitionThreadCurrent<IcfgLocation>> forkCurrentThreads,
			final List<IIcfgJoinTransitionThreadCurrent<IcfgLocation>> joinCurrentThreads) {
		final UnmodifiableTransFormula transFormula =
				TransFormulaBuilder.constructCopy(managedScript, edge.getTransformula(), varReplacement);
		if (edge instanceof IcfgInternalTransition) {
			final UnmodifiableTransFormula transFormulaWithBE = TransFormulaBuilder.constructCopy(managedScript,
					((IcfgInternalTransition) edge).getTransitionFormulaWithBranchEncoders(), varReplacement);
			return icfgEdgeFactory.createInternalTransition(source, target, null, transFormula, transFormulaWithBE);
		}
		if (edge instanceof IcfgForkThreadCurrentTransition) {
			final IcfgForkThreadCurrentTransition oldForkEdge = (IcfgForkThreadCurrentTransition) edge;
			final ForkSmtArguments newForkSmtArguments =
					copyForkSmtArguments(oldForkEdge.getForkSmtArguments(), varReplacement, managedScript);
			final IcfgForkThreadCurrentTransition newForkEdge = icfgEdgeFactory.createForkThreadCurrentTransition(
					source, target, null, transFormula, newForkSmtArguments, oldForkEdge.getNameOfForkedProcedure());
			// add to thread instance mapping
			forkCurrentThreads.add(newForkEdge);
			final List<ThreadInstance> threadInstances = threadInstanceMap.get(oldForkEdge);
			assert threadInstances != null;
			threadInstanceMap.put(newForkEdge, threadInstances);
			return newForkEdge;
		}
		if (edge instanceof IcfgJoinThreadCurrentTransition) {
			final JoinSmtArguments newForkSmtArguments = copyJoinSmtArguments(
					((IcfgJoinThreadCurrentTransition) edge).getJoinSmtArguments(), varReplacement, managedScript);
			final IcfgJoinThreadCurrentTransition newJoinEdge = icfgEdgeFactory
					.createJoinThreadCurrentTransition(source, target, null, transFormula, newForkSmtArguments);
			// add to join list
			joinCurrentThreads.add(newJoinEdge);
			return newJoinEdge;
		}
		if (edge instanceof IcfgCallTransition) {
			throw new UnsupportedOperationException(String.format(
					"%s does not support %s. Calls and returns should habe been removed by inlining. "
							+ "(Did the inlining fail because this program is recursive.)",
					ProcedureMultiplier.class.getSimpleName(), edge.getClass().getSimpleName()));
		}
		throw new UnsupportedOperationException(
				ProcedureMultiplier.class.getSimpleName() + " does not support " + edge.getClass().getSimpleName());
	}

	private static IcfgLocation getOrConstructLocationCopy(final IcfgLocation originalLocation,
			final Map<IcfgLocation, IcfgLocation> old2newLoc, final BasicIcfg<IcfgLocation> icfg, final String newProc,
			final BlockEncodingBacktranslator backtranslator) {
		return old2newLoc.computeIfAbsent(originalLocation,
				x -> constructLocationCopy(x, icfg, newProc, backtranslator));
	}

	private static IcfgLocation constructLocationCopy(final IcfgLocation originalLocation,
			final BasicIcfg<IcfgLocation> icfg, final String newProc,
			final BlockEncodingBacktranslator backtranslator) {
		final String proc = originalLocation.getProcedure();
		final IcfgLocation newLoc = new IcfgLocation(originalLocation.getDebugIdentifier(), newProc);
		ModelUtils.copyAnnotations(originalLocation, newLoc);
		backtranslator.mapLocations(newLoc, originalLocation);
		final boolean isInitial = icfg.getInitialNodes().contains(originalLocation);
		final boolean isError = icfg.getProcedureErrorNodes().get(proc).contains(originalLocation);
		final boolean isProcEntry = icfg.getProcedureEntryNodes().get(proc).equals(originalLocation);
		final boolean isProcExit = icfg.getProcedureExitNodes().get(proc).equals(originalLocation);
		final boolean isLoopLocation = icfg.getLoopLocations().contains(originalLocation);
		icfg.addLocation(newLoc, isInitial, isError, isProcEntry, isProcExit, isLoopLocation);
		return newLoc;
	}

	private static ILocalProgramVar constructVariableCopy(final ILocalProgramVar localVar, final String procedureCopy,
			final ManagedScript managedScript, final Map<ILocalProgramVar, ILocalProgramVar> procOldVar2NewVar,
			final Map<Term, Term> variableBacktranslationMapping, final DefaultIcfgSymbolTable symbolTable,
			final Object lockOwner) {
		final ILocalProgramVar localVarCopy = ProgramVarUtils.constructLocalProgramVar(localVar.getIdentifier(),
				procedureCopy, localVar.getSort(), managedScript, lockOwner);
		procOldVar2NewVar.put(localVar, localVarCopy);
		variableBacktranslationMapping.put(localVarCopy.getTermVariable(), localVar.getTermVariable());
		symbolTable.add(localVarCopy);
		return localVarCopy;
	}

	private static ForkSmtArguments copyForkSmtArguments(final ForkSmtArguments forkSmtArguments,
			final Map<ILocalProgramVar, ILocalProgramVar> map, final ManagedScript managedScript) {
		final Map<Term, Term> defaultVariableMapping = constructDefaultVariableMapping(map);
		final MultiTermResult newThreadIdArguments =
				copyMultiTermResult(forkSmtArguments.getThreadIdArguments(), defaultVariableMapping, managedScript);
		final MultiTermResult newProcedureArguments =
				copyMultiTermResult(forkSmtArguments.getProcedureArguments(), defaultVariableMapping, managedScript);
		return new ForkSmtArguments(newThreadIdArguments, newProcedureArguments);
	}

	private static JoinSmtArguments copyJoinSmtArguments(final JoinSmtArguments joinSmtArguments,
			final Map<ILocalProgramVar, ILocalProgramVar> map, final ManagedScript managedScript) {
		final Map<Term, Term> defaultVariableMapping = constructDefaultVariableMapping(map);
		final MultiTermResult newThreadIdArguments =
				copyMultiTermResult(joinSmtArguments.getThreadIdArguments(), defaultVariableMapping, managedScript);
		final List<IProgramVar> newAssignmentLhs = joinSmtArguments.getAssignmentLhs().stream()
				.map(x -> x.isGlobal() ? x : map.get(x)).collect(Collectors.toList());
		return new JoinSmtArguments(newThreadIdArguments, newAssignmentLhs);
	}

	private static MultiTermResult copyMultiTermResult(final MultiTermResult oldProcedureArguments,
			final Map<Term, Term> defaultVariableMadefaultVariableMappingpping2, final ManagedScript managedScript) {
		final UnaryOperator<Term> subst =
				(x -> Substitution.apply(managedScript, defaultVariableMadefaultVariableMappingpping2, x));
		final Term[] terms = Arrays.stream(oldProcedureArguments.getTerms()).map(subst).toArray(Term[]::new);
		final Collection<TermVariable> auxiliaryVars = oldProcedureArguments.getAuxiliaryVars();
		final Map<String, ILocation> overapproximations = oldProcedureArguments.getOverappoximations();
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
