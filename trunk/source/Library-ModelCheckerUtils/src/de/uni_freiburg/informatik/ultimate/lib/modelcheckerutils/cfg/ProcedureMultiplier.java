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
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.LocalBoogieVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Expression2Term.MultiTermResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadCurrentTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgJoinThreadCurrentTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IForkActionThreadCurrent.ForkSmtArguments;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IJoinActionThreadCurrent.JoinSmtArguments;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Modifies a given {@link IIcfg} by adding copies of existing procedures.
 * <p>
 * Copies are constructed according to the {@link HashRelation} argument "copyDirectives". If the relation contains the
 * pair (foo, bar) we construct a copy of the procedure "foo" and the identifier of the copy is "bar".
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
 */
public class ProcedureMultiplier {

	public ProcedureMultiplier(final IUltimateServiceProvider services, final BasicIcfg<IcfgLocation> icfg,
			final HashRelation<String, String> copyDirectives, final BlockEncodingBacktranslator backtranslator,
			final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, ThreadInstance> threadInstanceMap,
			final List<IIcfgForkTransitionThreadCurrent<IcfgLocation>> forkCurrentThreads,
			final List<IIcfgJoinTransitionThreadCurrent<IcfgLocation>> joinCurrentThreads) {
		super();
		final IcfgEdgeFactory icfgEdgeFactory = icfg.getCfgSmtToolkit().getIcfgEdgeFactory();
		final Map<String, List<ILocalProgramVar>> inParams = new HashMap<>(icfg.getCfgSmtToolkit().getInParams());
		final Map<String, List<ILocalProgramVar>> outParams = new HashMap<>(icfg.getCfgSmtToolkit().getOutParams());
		final Set<String> procedures = new HashSet<>(icfg.getCfgSmtToolkit().getProcedures());
		final SmtFunctionsAndAxioms smtSymbols = icfg.getCfgSmtToolkit().getSmtFunctionsAndAxioms();
		final DefaultIcfgSymbolTable symbolTable = new DefaultIcfgSymbolTable(icfg.getCfgSmtToolkit().getSymbolTable(),
				procedures);
		final ManagedScript managedScript = icfg.getCfgSmtToolkit().getManagedScript();
		final HashRelation<String, IProgramNonOldVar> proc2globals =
				new HashRelation<>(icfg.getCfgSmtToolkit().getModifiableGlobalsTable().getProcToGlobals());

		final Map<ILocalProgramVar, ILocalProgramVar> newVar2OldVar = new HashMap<>();
		final Map<String, Map<ILocalProgramVar, ILocalProgramVar>> oldVar2newVar = new HashMap<>();
		final Map<Term, Term> variableBacktranslationMapping = new HashMap<>();
		icfg.getCfgSmtToolkit().getManagedScript().lock(this);
		for (final String proc : copyDirectives.getDomain()) {
			assert icfg.getCfgSmtToolkit().getProcedures().contains(proc) : "procedure " + proc + " missing";
			for (final String copyIdentifier : copyDirectives.getImage(proc)) {
				icfg.addProcedure(copyIdentifier);
				final Map<ILocalProgramVar, ILocalProgramVar> procOldVar2NewVar = new HashMap<>();
				procedures.add(copyIdentifier);
				final List<ILocalProgramVar> inParamsOfCopy = new ArrayList<>();
				for (final ILocalProgramVar inParam : inParams.get(proc)) {
					final ILocalProgramVar inParamCopy =
							constructCopy(inParam, copyIdentifier, icfg.getCfgSmtToolkit().getManagedScript(), this);
					inParamsOfCopy.add(inParamCopy);
					newVar2OldVar.put(inParamCopy, inParam);
					procOldVar2NewVar.put(inParam, inParamCopy);
					variableBacktranslationMapping.put(inParamCopy.getTermVariable(), inParam.getTermVariable());
					symbolTable.add(inParamCopy);
				}
				inParams.put(copyIdentifier, inParamsOfCopy);
				final List<ILocalProgramVar> outParamsOfCopy = new ArrayList<>();
				for (final ILocalProgramVar outParam : outParams.get(proc)) {
					final ILocalProgramVar outParamCopy =
							constructCopy(outParam, copyIdentifier, icfg.getCfgSmtToolkit().getManagedScript(), this);
					outParamsOfCopy.add(outParamCopy);
					newVar2OldVar.put(outParamCopy, outParam);
					procOldVar2NewVar.put(outParam, outParamCopy);
					variableBacktranslationMapping.put(outParamCopy.getTermVariable(), outParam.getTermVariable());
					symbolTable.add(outParamCopy);
				}
				outParams.put(copyIdentifier, outParamsOfCopy);
				for (final ILocalProgramVar localVar : icfg.getCfgSmtToolkit().getSymbolTable().getLocals(proc)) {
					if (!procOldVar2NewVar.containsKey(localVar)) {
						final ILocalProgramVar localVarCopy = constructCopy(localVar, copyIdentifier,
								icfg.getCfgSmtToolkit().getManagedScript(), this);
						procOldVar2NewVar.put(localVar, localVarCopy);
						variableBacktranslationMapping.put(localVarCopy.getTermVariable(), localVar.getTermVariable());
						symbolTable.add(localVarCopy);
					}
				}
				final List<IProgramNonOldVar> modifiableGlobals = new ArrayList<>();
				for (final IProgramNonOldVar modifiableGlobal : proc2globals.getImage(proc)) {
					modifiableGlobals.add(modifiableGlobal);
				}
				for (final IProgramNonOldVar modifiableGlobal : modifiableGlobals) {
					proc2globals.addPair(copyIdentifier, modifiableGlobal);
				}
				oldVar2newVar.put(copyIdentifier, procOldVar2NewVar);
			}
		}
		backtranslator.setTermTranslator(
				x -> new Substitution(icfg.getCfgSmtToolkit().getManagedScript(), variableBacktranslationMapping)
						.transform(x));
		icfg.getCfgSmtToolkit().getManagedScript().unlock(this);

		final ModifiableGlobalsTable modifiableGlobalsTable = new ModifiableGlobalsTable(proc2globals);
		final CfgSmtToolkit newCfgSmtToolkit =
				new CfgSmtToolkit(modifiableGlobalsTable, managedScript, symbolTable, procedures, inParams, outParams,
						icfgEdgeFactory, icfg.getCfgSmtToolkit().getConcurrencyInformation(), smtSymbols);
		final Map<IcfgLocation, IcfgLocation> newLoc2OldLoc = new HashMap<>();
		for (final String proc : copyDirectives.getDomain()) {
			final IcfgLocation procEntry = icfg.getProcedureEntryNodes().get(proc);
			final List<IcfgLocation> procLocs =
					new IcfgLocationIterator<>(procEntry).asStream().collect(Collectors.toList());
			for (final String copyIdentifier : copyDirectives.getImage(proc)) {
				final Map<IcfgLocation, IcfgLocation> procOldLoc2NewLoc = new HashMap<>();
				// add locations
				for (final IcfgLocation oldLoc : procLocs) {
					final IcfgLocation newLoc = constructCopy(oldLoc, copyIdentifier, backtranslator);
					newLoc2OldLoc.put(newLoc, oldLoc);
					procOldLoc2NewLoc.put(oldLoc, newLoc);
					final boolean isInitial = icfg.getInitialNodes().contains(oldLoc);
					final boolean isError = icfg.getProcedureErrorNodes().get(proc).contains(oldLoc);
					final boolean isProcEntry = icfg.getProcedureEntryNodes().get(proc).equals(oldLoc);
					final boolean isProcExit = icfg.getProcedureExitNodes().get(proc).equals(oldLoc);
					final boolean isLoopLocation = icfg.getLoopLocations().contains(oldLoc);
					icfg.addLocation(newLoc, isInitial, isError, isProcEntry, isProcExit, isLoopLocation);
				}
				// add edges
				for (final IcfgLocation oldLoc : procLocs) {
					for (final IcfgEdge outEdge : oldLoc.getOutgoingEdges()) {
						if (outEdge instanceof IcfgInternalTransition) {
							final IcfgInternalTransition oldInternalEdge = (IcfgInternalTransition) outEdge;
							final IcfgLocation source = procOldLoc2NewLoc.get(oldInternalEdge.getSource());
							final IcfgLocation target = procOldLoc2NewLoc.get(oldInternalEdge.getTarget());
							final IPayload payload = null;
							final UnmodifiableTransFormula transFormula = TransFormulaBuilder.constructCopy(
									managedScript, outEdge.getTransformula(), oldVar2newVar.get(copyIdentifier));
							final IcfgInternalTransition newInternalEdge =
									icfgEdgeFactory.createInternalTransition(source, target, payload, transFormula);
							backtranslator.mapEdges(newInternalEdge, oldInternalEdge);
							ModelUtils.copyAnnotations(oldInternalEdge, newInternalEdge);
							source.addOutgoing(newInternalEdge);
							target.addIncoming(newInternalEdge);
						} else if (outEdge instanceof IcfgForkThreadCurrentTransition) {
							// mainly copy and paste form IcfgInternalTransition
							final IcfgForkThreadCurrentTransition oldForkEdge =
									(IcfgForkThreadCurrentTransition) outEdge;
							final IcfgLocation source = procOldLoc2NewLoc.get(oldForkEdge.getSource());
							final IcfgLocation target = procOldLoc2NewLoc.get(oldForkEdge.getTarget());
							final IPayload payload = null;
							final UnmodifiableTransFormula transFormula = TransFormulaBuilder.constructCopy(
									managedScript, outEdge.getTransformula(), oldVar2newVar.get(copyIdentifier));
							final ForkSmtArguments newForkSmtArguments =
									copyForkSmtArguments(oldForkEdge.getForkSmtArguments(),
											oldVar2newVar.get(copyIdentifier), managedScript);
							final IcfgForkThreadCurrentTransition newForkEdge =
									icfgEdgeFactory.createForkThreadCurrentTransition(source, target, payload,
											transFormula, newForkSmtArguments, oldForkEdge.getNameOfForkedProcedure());
							backtranslator.mapEdges(newForkEdge, oldForkEdge);
							ModelUtils.copyAnnotations(oldForkEdge, newForkEdge);
							source.addOutgoing(newForkEdge);
							target.addIncoming(newForkEdge);
							// add to thread instance mapping
							forkCurrentThreads.add(newForkEdge);
							final ThreadInstance threadInstance = threadInstanceMap.get(oldForkEdge);
							assert threadInstance != null;
							threadInstanceMap.put(newForkEdge, threadInstance);
						} else if (outEdge instanceof IcfgJoinThreadCurrentTransition) {
							// mainly copy and paste form IcfgInternalTransition
							final IcfgJoinThreadCurrentTransition oldJoinEdge =
									(IcfgJoinThreadCurrentTransition) outEdge;
							final IcfgLocation source = procOldLoc2NewLoc.get(oldJoinEdge.getSource());
							final IcfgLocation target = procOldLoc2NewLoc.get(oldJoinEdge.getTarget());
							final IPayload payload = null;
							final UnmodifiableTransFormula transFormula = TransFormulaBuilder.constructCopy(
									managedScript, outEdge.getTransformula(), oldVar2newVar.get(copyIdentifier));
							final JoinSmtArguments newForkSmtArguments =
									copyJoinSmtArguments(oldJoinEdge.getJoinSmtArguments(),
											oldVar2newVar.get(copyIdentifier), managedScript);
							final IcfgJoinThreadCurrentTransition newJoinEdge =
									icfgEdgeFactory.createJoinThreadCurrentTransition(source, target, payload,
											transFormula, newForkSmtArguments);
							backtranslator.mapEdges(newJoinEdge, oldJoinEdge);
							ModelUtils.copyAnnotations(oldJoinEdge, newJoinEdge);
							source.addOutgoing(newJoinEdge);
							target.addIncoming(newJoinEdge);
							// add to join list
							joinCurrentThreads.add(newJoinEdge);
						} else {
							throw new UnsupportedOperationException(this.getClass().getSimpleName()
									+ " does not support " + outEdge.getClass().getSimpleName());
						}
					}
				}
			}
		}
		icfg.setCfgSmtToolkit(newCfgSmtToolkit);
	}

	private ForkSmtArguments copyForkSmtArguments(final ForkSmtArguments forkSmtArguments,
			final Map<ILocalProgramVar, ILocalProgramVar> map, final ManagedScript managedScript) {
		final Map<Term, Term> defaultVariableMapping = constructDefaultVariableMapping(map);
		final MultiTermResult newThreadIdArguments =
				copyMultiTermResult(forkSmtArguments.getThreadIdArguments(), defaultVariableMapping, managedScript);
		final MultiTermResult newProcedureArguments =
				copyMultiTermResult(forkSmtArguments.getProcedureArguments(), defaultVariableMapping, managedScript);
		return new ForkSmtArguments(newThreadIdArguments, newProcedureArguments);
	}

	private JoinSmtArguments copyJoinSmtArguments(final JoinSmtArguments joinSmtArguments,
			final Map<ILocalProgramVar, ILocalProgramVar> map, final ManagedScript managedScript) {
		final Map<Term, Term> defaultVariableMapping = constructDefaultVariableMapping(map);
		final MultiTermResult newThreadIdArguments =
				copyMultiTermResult(joinSmtArguments.getThreadIdArguments(), defaultVariableMapping, managedScript);
		final List<IProgramVar> newAssignmentLhs =
				joinSmtArguments.getAssignmentLhs().stream().map(map::get).collect(Collectors.toList());
		return new JoinSmtArguments(newThreadIdArguments, newAssignmentLhs);
	}

	private MultiTermResult copyMultiTermResult(final MultiTermResult oldProcedureArguments,
			final Map<Term, Term> defaultVariableMadefaultVariableMappingpping2, final ManagedScript managedScript) {
		final Term[] terms = new Substitution(managedScript, defaultVariableMadefaultVariableMappingpping2)
				.transform(Arrays.asList(oldProcedureArguments.getTerms()))
				.toArray(new Term[oldProcedureArguments.getTerms().length]);
		final Collection<TermVariable> auxiliaryVars = oldProcedureArguments.getAuxiliaryVars();
		final Map<String, ILocation> overapproximations = oldProcedureArguments.getOverappoximations();
		final MultiTermResult copy = new MultiTermResult(overapproximations, auxiliaryVars, terms);
		return copy;
	}

	private Map<Term, Term> constructDefaultVariableMapping(final Map<ILocalProgramVar, ILocalProgramVar> map) {
		final Map<Term, Term> result = new HashMap<>();
		for (final Entry<ILocalProgramVar, ILocalProgramVar> entry : map.entrySet()) {
			result.put(entry.getKey().getTermVariable(), entry.getValue().getTermVariable());
		}
		return result;
	}

	private static IcfgLocation constructCopy(final IcfgLocation oldLoc, final String copy,
			final BlockEncodingBacktranslator backtranslator) {
		final IcfgLocation newLoc = new IcfgLocation(oldLoc.getDebugIdentifier(), copy);
		ModelUtils.copyAnnotations(oldLoc, newLoc);
		backtranslator.mapLocations(newLoc, oldLoc);
		return newLoc;
	}

	/**
	 * FIXME Merge
	 */
	private ILocalProgramVar constructCopy(final ILocalProgramVar localVar, final String copyIdentifier,
			final ManagedScript managedScript, final Object lockOwner) {
		final Sort sort = localVar.getSort();
		final String name = ProgramVarUtils.buildBoogieVarName(localVar.getIdentifier(), copyIdentifier, false, false);

		final TermVariable termVariable = managedScript.getScript().variable(name, sort);

		final ApplicationTerm defaultConstant =
				ProgramVarUtils.constructDefaultConstant(managedScript, lockOwner, sort, name);
		final ApplicationTerm primedConstant =
				ProgramVarUtils.constructPrimedConstant(managedScript, lockOwner, sort, name);

		final LocalBoogieVar bv = new LocalBoogieVar(localVar.getIdentifier(), copyIdentifier, null, termVariable,
				defaultConstant, primedConstant);
		return bv;
	}

	private String construtCopyIdentifier(final String proc, final String suffix) {
		return proc + "_" + suffix;
	}

	public static HashRelation<String, String>
			generateCopyDirectives(final Collection<ThreadInstance> threadInstances) {
		final HashRelation<String, String> result = new HashRelation<>();
		for (final ThreadInstance ti : threadInstances) {
			result.addPair(ti.getThreadTemplateName(), ti.getThreadInstanceName());
		}
		return result;
	}

}
