/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogieOutput;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quad;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Write path program to a Boogie file
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PathProgramDumper {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	ConstructionCache.IValueConstruction<IcfgLocation, String> mLoc2LabelVC = new ConstructionCache.IValueConstruction<IcfgLocation, String>() {

		int mCounter = 0;

		@Override
		public String constructValue(final IcfgLocation key) {
			final String result = "loc" + String.valueOf(mCounter);
			mCounter++;
			return result;
		}

	};
	private final ConstructionCache<IcfgLocation, String> mLoc2LabelId = new ConstructionCache<>(mLoc2LabelVC);

	public PathProgramDumper(final IIcfg<?> icfg, final IUltimateServiceProvider services,
			final NestedRun<? extends IAction, IPredicate> run, final String filename) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		if (!(icfg instanceof BoogieIcfgContainer)) {
			throw new UnsupportedOperationException("PathProgramDumper currently needs BoogieIcfgContainer");
		}

		final Set<? extends IcfgEdge> allowedTransitions = extractTransitionsFromRun(run.getWord());
		final PathProgram.PathProgramConstructionResult ppResult = PathProgram
				.constructPathProgram("PathInvariantsPathProgram", icfg, allowedTransitions);
		final IIcfg<IcfgLocation> pathProgram = ppResult.getPathProgram();

		final BoogieIcfgContainer boogieIcfg = (BoogieIcfgContainer) icfg;
		final List<Declaration> newDeclarations = new ArrayList<>();
		final Set<IProgramVar> globalVars = new HashSet<>();
		for (final Entry<String, IcfgLocation> entry : pathProgram.getProcedureEntryNodes().entrySet()) {
			final Pair<Procedure, Set<IProgramVar>> newImplAndGlobalVars = constructNewImplementation(entry.getKey(),
					entry.getValue(), boogieIcfg, pathProgram.getProcedureErrorNodes().get(entry.getKey()));
			newDeclarations.add(newImplAndGlobalVars.getFirst());
			globalVars.addAll(newImplAndGlobalVars.getSecond());

			final Procedure spec = boogieIcfg.getBoogieDeclarations().getProcSpecification().get(entry.getKey());
			final Procedure impl = boogieIcfg.getBoogieDeclarations().getProcImplementation().get(entry.getKey());
			if (spec != impl) {
				newDeclarations.add(spec);
			}

		}

		newDeclarations.addAll(0, Arrays.asList(
				filter(boogieIcfg.getBoogieDeclarations().getGlobalVarDeclarations(), extractIdentifiers(globalVars))));
		newDeclarations.addAll(0, boogieIcfg.getBoogieDeclarations().getFunctionDeclarations());
		newDeclarations.addAll(0, boogieIcfg.getBoogieDeclarations().getAxioms());
		newDeclarations.addAll(0, boogieIcfg.getBoogieDeclarations().getConstDeclarations());
		newDeclarations.addAll(0, boogieIcfg.getBoogieDeclarations().getTypeDeclarations());
		final Unit unit = new Unit(constructNewLocation(),
				newDeclarations.toArray(new Declaration[newDeclarations.size()]));

		final File file = new File(filename);
		mLogger.warn("Writing path program to file " + file.getAbsolutePath());

		PrintWriter writer;
		try {
			writer = new PrintWriter(new FileWriter(file));
			final BoogieOutput output = new BoogieOutput(writer);
			output.printBoogieProgram(unit);
			writer.close();
		} catch (final IOException e) {
			throw new AssertionError(e);
		}

	}

	private Pair<Procedure, Set<IProgramVar>> constructNewImplementation(final String proc, final IcfgLocation entryLoc,
			final BoogieIcfgContainer boogieIcfg, final Set<IcfgLocation> errorLocs) {
		final Procedure impl = boogieIcfg.getBoogieDeclarations().getProcImplementation().get(proc);
		final Body body = impl.getBody();

		final Triple<List<Statement>, Set<IProgramVar>, Set<IProgramVar>> varsAndNewSt = constructProcedureStatements(
				entryLoc, errorLocs);
		final List<Statement> newStatements = varsAndNewSt.getFirst();

		final VariableDeclaration[] localVars = filter(Arrays.asList(body.getLocalVars()),
				extractIdentifiers(varsAndNewSt.getSecond()));
		final Body newBody = new Body(constructNewLocation(), localVars,
				newStatements.toArray(new Statement[newStatements.size()]));
		final Procedure newProc = new Procedure(constructNewLocation(), impl.getAttributes(), impl.getIdentifier(),
				impl.getTypeParams(), impl.getInParams(), impl.getOutParams(),
				filterModifiesSpecifications(impl.getSpecification(), extractIdentifiers(varsAndNewSt.getThird())),
				newBody);
		return new Pair<>(newProc, varsAndNewSt.getThird());
	}

	private Specification[] filterModifiesSpecifications(final Specification[] specification,
			final Set<String> globalVars) {
		final List<Specification> result = new ArrayList<>();
		for (final Specification spec : specification) {
			if (spec instanceof ModifiesSpecification) {
				result.add(filter((ModifiesSpecification) spec, globalVars));
			} else {
				result.add(spec);
			}
		}
		return result.toArray(new Specification[result.size()]);
	}

	private ModifiesSpecification filter(final ModifiesSpecification modSpec, final Set<String> globalVars) {
		final List<VariableLHS> filteredIdentifiers = new ArrayList<>();
		for (final VariableLHS varLhs : modSpec.getIdentifiers()) {
			if (globalVars.contains(varLhs.getIdentifier())) {
				filteredIdentifiers.add(varLhs);
			}
		}
		return new ModifiesSpecification(modSpec.getLocation(), modSpec.isFree(),
				filteredIdentifiers.toArray(new VariableLHS[filteredIdentifiers.size()]));
	}

	private Set<String> extractIdentifiers(final Set<IProgramVar> vars) {
		final Set<String> result = new HashSet<>();
		for (final IProgramVar var : vars) {
			if (var instanceof IProgramOldVar) {
				result.add(((IProgramOldVar) var).getIdentifierOfNonOldVar());
			} else if (var instanceof IProgramNonOldVar) {
				result.add(((IProgramNonOldVar) var).getIdentifier());
			} else if (var instanceof ILocalProgramVar) {
				result.add(((ILocalProgramVar) var).getIdentifier());
			} else {
				throw new IllegalArgumentException("unknown type of var " + var);
			}
		}
		return result;
	}

	private VariableDeclaration[] filter(final List<VariableDeclaration> localVars, final Set<String> vars) {
		final List<VariableDeclaration> result = new ArrayList<>();
		for (final VariableDeclaration varDecl : localVars) {
			final VariableDeclaration newDecl = filter(varDecl, vars);
			if (newDecl != null) {
				result.add(newDecl);
			}
		}
		return result.toArray(new VariableDeclaration[result.size()]);
	}

	private VariableDeclaration filter(final VariableDeclaration varDecl, final Set<String> vars) {
		final List<VarList> resultVarLists = new ArrayList<>();
		for (final VarList varList : varDecl.getVariables()) {
			final String[] newIdentifiers = filter(varList.getIdentifiers(), vars);
			if (newIdentifiers.length > 0) {
				resultVarLists.add(new VarList(varList.getLocation(), newIdentifiers, varList.getType()));
			}
		}
		if (resultVarLists.isEmpty()) {
			return null;
		} else {
			return new VariableDeclaration(varDecl.getLocation(), new Attribute[0],
					resultVarLists.toArray(new VarList[resultVarLists.size()]));
		}
	}

	private String[] filter(final String[] identifiers, final Set<String> vars) {
		final Predicate<? super String> pred = (x -> vars.contains(x));
		return Arrays.stream(identifiers).filter(pred).toArray(size -> new String[size]);
	}

	private Triple<List<Statement>, Set<IProgramVar>, Set<IProgramVar>> constructProcedureStatements(
			final IcfgLocation initialNode, final Set<IcfgLocation> errorLocs) {
		final ArrayDeque<IcfgLocation> worklist = new ArrayDeque<>();
		final Set<IcfgLocation> added = new HashSet<>();
		worklist.add(initialNode);
		added.add(initialNode);
		final List<Statement> newStatements = new ArrayList<>();
		final Set<IProgramVar> localVars = new HashSet<>();
		final Set<IProgramVar> globalVars = new HashSet<>();
		while (!worklist.isEmpty()) {
			final IcfgLocation node = worklist.remove();
			newStatements.add(constructLabel(node));
			if (errorLocs.contains(node)) {
				newStatements.add(
						new AssertStatement(constructNewLocation(), new BooleanLiteral(constructNewLocation(), false)));
				assert node.getOutgoingEdges().isEmpty() : "error loc with outgoing transitions";
			}
			if (node.getOutgoingEdges().isEmpty()) {
				// do nothing, no successor
			} else if (node.getOutgoingEdges().size() == 1) {
				final IcfgEdge edge = node.getOutgoingEdges().get(0);
				processTransition(worklist, added, newStatements, localVars, globalVars, edge);
			} else {
				final String[] transitionStartLabels = new String[node.getOutgoingEdges().size()];
				for (int i = 0; i < node.getOutgoingEdges().size(); i++) {
					final String transitionStartLabel = constructLabelId(node, i);
					transitionStartLabels[i] = transitionStartLabel;
				}
				if (!node.getOutgoingEdges().isEmpty()) {
					newStatements.add(new GotoStatement(constructNewLocation(), transitionStartLabels));
				}
				for (int i = 0; i < node.getOutgoingEdges().size(); i++) {
					final IcfgEdge edge = node.getOutgoingEdges().get(i);
					newStatements.add(constructLabel(node, i));
					processTransition(worklist, added, newStatements, localVars, globalVars, edge);
				}
			}
		}
		return new Triple<>(newStatements, localVars, globalVars);
	}

	private void processTransition(final ArrayDeque<IcfgLocation> worklist, final Set<IcfgLocation> added,
			final List<Statement> result, final Set<IProgramVar> localvars, final Set<IProgramVar> globalVars,
			final IcfgEdge edge) {
		final Quad<List<Statement>, Set<IProgramVar>, Set<IProgramVar>, IcfgLocation> transResult = constructTransitionStatements(
				edge);
		result.addAll(transResult.getFirst());
		localvars.addAll(transResult.getSecond());
		globalVars.addAll(transResult.getThird());
		if (!added.contains(transResult.getFourth())) {
			worklist.add(transResult.getFourth());
			added.add(transResult.getFourth());
		}
	}

	private String constructLabelId(final IcfgLocation node) {
		return mLoc2LabelId.getOrConstruct(node);
	}

	private String constructLabelId(final IcfgLocation node, final int i) {
		return mLoc2LabelId.getOrConstruct(node) + "_" + i;
	}

	private Statement constructLabel(final IcfgLocation node) {
		return new Label(constructNewLocation(), constructLabelId(node));
	}

	private Statement constructLabel(final IcfgLocation node, final int i) {
		return new Label(constructNewLocation(), constructLabelId(node, i));
	}

	private Quad<List<Statement>, Set<IProgramVar>, Set<IProgramVar>, IcfgLocation> constructTransitionStatements(
			IcfgEdge edge) {
		final List<Statement> statements = new ArrayList<>();
		final Set<IProgramVar> localVars = new HashSet<>();
		final Set<IProgramVar> globalVars = new HashSet<>();
		addStatementsAndVariables(edge, statements, localVars, globalVars);
		while (isBridgingLocation(edge.getTarget())) {
			edge = edge.getTarget().getOutgoingEdges().get(0);
			addStatementsAndVariables(edge, statements, localVars, globalVars);
		}
		final String targetLabel = constructLabelId(edge.getTarget());
		statements.add(new GotoStatement(constructNewLocation(), new String[] { targetLabel }));
		return new Quad<>(statements, localVars, globalVars, edge.getTarget());
	}

	private void addStatementsAndVariables(final IcfgEdge edge, final List<Statement> statements,
			final Set<IProgramVar> localVars, final Set<IProgramVar> globalVars) {
		final StatementSequence stseq = (StatementSequence) edge.getLabel();
		addVars(stseq.getTransformula().getInVars().keySet(), localVars, globalVars);
		addVars(stseq.getTransformula().getOutVars().keySet(), localVars, globalVars);
		for (final Statement st : stseq.getStatements()) {
			statements.add(st);
		}
	}

	/**
	 * Given a set of {@link IProgramVar}, sort them into localVars and
	 * globalVars.
	 */
	private void addVars(final Set<IProgramVar> vars, final Set<IProgramVar> localVars,
			final Set<IProgramVar> globalVars) {
		for (final IProgramVar var : vars) {
			if ((var instanceof IProgramOldVar) || (var instanceof IProgramNonOldVar)) {
				globalVars.add(var);
			} else if (var instanceof ILocalProgramVar) {
				localVars.add(var);
			} else {
				throw new IllegalArgumentException("unknown type of var " + var);
			}
		}
	}

	/**
	 * @return true iff location has exactly one outgoing edge and one incoming
	 *         edge
	 */
	private boolean isBridgingLocation(final IcfgLocation loc) {
		return loc.getIncomingEdges().size() == 1 && loc.getOutgoingEdges().size() == 1;
	}

	private ILocation constructNewLocation() {
		return new DefaultLocation();
	}

	private Set<? extends IcfgEdge> extractTransitionsFromRun(final NestedWord<? extends IAction> word) {
		final Set<IcfgEdge> result = new HashSet<>();
		for (final IAction letter : word) {
			final StatementSequence sc = (StatementSequence) letter;
			result.add(sc);
		}
		return result;
	}

}
