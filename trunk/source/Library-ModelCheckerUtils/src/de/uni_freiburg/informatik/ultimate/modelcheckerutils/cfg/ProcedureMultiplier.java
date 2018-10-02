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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.LocalBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * @author heizmann@informatik.uni-freiburg.de
 */

public class ProcedureMultiplier {

	public ProcedureMultiplier(final IUltimateServiceProvider services, final BasicIcfg<IcfgLocation> icfg,
			final HashRelation<String, String> copyDirectives, final BlockEncodingBacktranslator backtranslator) {
		super();
		final IcfgEdgeFactory icfgEdgeFactory = icfg.getCfgSmtToolkit().getIcfgEdgeFactory();
		final Map<String, List<ILocalProgramVar>> inParams = new HashMap<>(icfg.getCfgSmtToolkit().getInParams());
		final Map<String, List<ILocalProgramVar>> outParams = new HashMap<>(icfg.getCfgSmtToolkit().getOutParams());
		final Set<String> procedures = new HashSet<>(icfg.getCfgSmtToolkit().getProcedures());
		final IPredicate axioms = icfg.getCfgSmtToolkit().getAxioms();
		final DefaultIcfgSymbolTable symbolTable = new DefaultIcfgSymbolTable(icfg.getSymboltable(), procedures);
		final ManagedScript managedScript = icfg.getCfgSmtToolkit().getManagedScript();
		final HashRelation<String, IProgramNonOldVar> proc2globals = new HashRelation<>(
				icfg.getCfgSmtToolkit().getModifiableGlobalsTable().getProcToGlobals());

		final Map<ILocalProgramVar, ILocalProgramVar> newVar2OldVar = new HashMap<>();
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
					final ILocalProgramVar inParamCopy = constructCopy(inParam, copyIdentifier,
							icfg.getCfgSmtToolkit().getManagedScript(), this);
					inParamsOfCopy.add(inParamCopy);
					newVar2OldVar.put(inParamCopy, inParam);
					procOldVar2NewVar.put(inParam, inParamCopy);
					variableBacktranslationMapping.put(inParamCopy.getTermVariable(), inParam.getTermVariable());
					symbolTable.add(inParamCopy);
				}
				inParams.put(copyIdentifier, inParamsOfCopy);
				final List<ILocalProgramVar> outParamsOfCopy = new ArrayList<>();
				for (final ILocalProgramVar outParam : outParams.get(proc)) {
					final ILocalProgramVar outParamCopy = constructCopy(outParam, copyIdentifier,
							icfg.getCfgSmtToolkit().getManagedScript(), this);
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
			}
		}
		backtranslator.setTermTranslator(
				x -> new Substitution(icfg.getCfgSmtToolkit().getManagedScript(), variableBacktranslationMapping)
				.transform(x));
		icfg.getCfgSmtToolkit().getManagedScript().unlock(this);

		final ModifiableGlobalsTable modifiableGlobalsTable = new ModifiableGlobalsTable(proc2globals);
		final CfgSmtToolkit newCfgSmtToolkit = new CfgSmtToolkit(modifiableGlobalsTable, managedScript, symbolTable,
				axioms, procedures, inParams, outParams, icfgEdgeFactory,
				icfg.getCfgSmtToolkit().getConcurrencyInformation());
		final Map<IcfgLocation, IcfgLocation> newLoc2OldLoc = new HashMap<>();
		for (final String proc : copyDirectives.getDomain()) {
			final IcfgLocation procEntry = icfg.getProcedureEntryNodes().get(proc);
			final List<IcfgLocation> procLocs = new IcfgLocationIterator<>(procEntry).asStream()
					.collect(Collectors.toList());
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
							final IcfgInternalTransition oldInternalOutEdge = (IcfgInternalTransition) outEdge;
							final IcfgLocation source = procOldLoc2NewLoc.get(oldInternalOutEdge.getSource());
							final IcfgLocation target = procOldLoc2NewLoc.get(oldInternalOutEdge.getTarget());
							final IPayload payload = null;
							final UnmodifiableTransFormula transFormula = TransFormulaBuilder.constructCopy(
									managedScript, outEdge.getTransformula(),
									DataStructureUtils.constructReverseMapping(newVar2OldVar));
							final IcfgInternalTransition newInternalOutEdge = icfgEdgeFactory
									.createInternalTransition(source, target, payload, transFormula);
							backtranslator.mapEdges(newInternalOutEdge, oldInternalOutEdge);
							source.addOutgoing(newInternalOutEdge);
							target.addIncoming(newInternalOutEdge);

						} else {
							throw new UnsupportedOperationException();
						}
					}
				}
			}
		}
		icfg.setCfgSmtToolkit(newCfgSmtToolkit);
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

		final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(managedScript, lockOwner, sort,
				name);
		final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(managedScript, lockOwner, sort,
				name);

		final LocalBoogieVar bv = new LocalBoogieVar(localVar.getIdentifier(), copyIdentifier, null, termVariable,
				defaultConstant, primedConstant);
		return bv;
	}

	private String construtCopyIdentifier(final String proc, final String suffix) {
		return proc + "_" + suffix;
	}

	public static HashRelation<String, String> generateCopyDirectives(
			final Collection<ThreadInstance> threadInstances) {
		final HashRelation<String, String> result = new HashRelation<>();
		for (final ThreadInstance ti : threadInstances) {
			result.addPair(ti.getThreadTemplateName(), ti.getThreadInstanceName());
		}
		return result;
	}

}
