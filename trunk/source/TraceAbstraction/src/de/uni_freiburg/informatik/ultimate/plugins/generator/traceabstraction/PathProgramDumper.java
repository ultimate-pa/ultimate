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
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogieOutput;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
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

	ConstructionCache.IValueConstruction<IcfgLocation, String> mLoc2LabelVC = 
			new ConstructionCache.IValueConstruction<IcfgLocation, String>() {

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
		for (final Entry<String, IcfgLocation> entry : pathProgram.getProcedureEntryNodes().entrySet()) {
			final Procedure newImpl = constructNewImplementation(entry.getKey(), entry.getValue(), boogieIcfg,
					pathProgram.getProcedureErrorNodes().get(entry.getKey()));
			newDeclarations.add(newImpl);

			final Procedure spec = boogieIcfg.getBoogieDeclarations().getProcSpecification().get(entry.getKey());
			final Procedure impl = boogieIcfg.getBoogieDeclarations().getProcImplementation().get(entry.getKey());
			if (spec != impl) {
				newDeclarations.add(spec);
			}

		}
		newDeclarations.addAll(boogieIcfg.getBoogieDeclarations().getAxioms());
		newDeclarations.addAll(boogieIcfg.getBoogieDeclarations().getConstDeclarations());
		newDeclarations.addAll(boogieIcfg.getBoogieDeclarations().getFunctionDeclarations());
		newDeclarations.addAll(boogieIcfg.getBoogieDeclarations().getGlobalVarDeclarations());
		newDeclarations.addAll(boogieIcfg.getBoogieDeclarations().getTypeDeclarations());
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

	private Procedure constructNewImplementation(final String proc, final IcfgLocation entryLoc,
			final BoogieIcfgContainer boogieIcfg, final Set<IcfgLocation> errorLocs) {
		final Procedure impl = boogieIcfg.getBoogieDeclarations().getProcImplementation().get(proc);
		final Body body = impl.getBody();
		final VariableDeclaration[] localVars = body.getLocalVars();
		final List<Statement> newStatements = constructProcedureStatements(entryLoc, errorLocs);

		final Body newBody = new Body(constructNewLocation(), localVars,
				newStatements.toArray(new Statement[newStatements.size()]));
		final Procedure result = new Procedure(constructNewLocation(), impl.getAttributes(), impl.getIdentifier(),
				impl.getTypeParams(), impl.getInParams(), impl.getOutParams(), impl.getSpecification(), newBody);
		return result;
	}

	private List<Statement> constructProcedureStatements(final IcfgLocation initialNode,
			final Set<IcfgLocation> errorLocs) {
		final ArrayDeque<IcfgLocation> worklist = new ArrayDeque<>();
		final Set<IcfgLocation> added = new HashSet<>();
		worklist.add(initialNode);
		added.add(initialNode);
		final List<Statement> result = new ArrayList<>();
		// currently unused, might be used after refactoring
		final Set<IProgramVar> vars = new HashSet<>();
		while (!worklist.isEmpty()) {
			final IcfgLocation node = worklist.remove();
			result.add(constructLabel(node));
			if (errorLocs.contains(node)) {
				result.add(
						new AssertStatement(constructNewLocation(), new BooleanLiteral(constructNewLocation(), false)));
				assert node.getOutgoingEdges().isEmpty() : "error loc with outgoing transitions";
			}
			if (node.getOutgoingEdges().isEmpty()) {
				// do nothing, no successor
			} else if (node.getOutgoingEdges().size() == 1) {
				final IcfgEdge edge = node.getOutgoingEdges().get(0);
				processTransition(worklist, added, result, vars, edge);
			} else {
				final String[] transitionStartLabels = new String[node.getOutgoingEdges().size()];
				for (int i = 0; i < node.getOutgoingEdges().size(); i++) {
					final String transitionStartLabel = constructLabelId(node, i);
					transitionStartLabels[i] = transitionStartLabel;
				}
				if (!node.getOutgoingEdges().isEmpty()) {
					result.add(new GotoStatement(constructNewLocation(), transitionStartLabels));
				}
				for (int i = 0; i < node.getOutgoingEdges().size(); i++) {
					final IcfgEdge edge = node.getOutgoingEdges().get(i);
					result.add(constructLabel(node, i));
					processTransition(worklist, added, result, vars, edge);
				}
			}
		}
		return result;
	}

	private void processTransition(final ArrayDeque<IcfgLocation> worklist,
			final Set<IcfgLocation> added, final List<Statement> result, final Set<IProgramVar> vars,
			final IcfgEdge edge) {
		final Triple<List<Statement>, Set<IProgramVar>, IcfgLocation> transResult = constructTransitionStatements(edge);
		result.addAll(transResult.getFirst());
		vars.addAll(transResult.getSecond());
		if (!added.contains(transResult.getThird())) {
			worklist.add(transResult.getThird());
			added.add(transResult.getThird());
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

	private Triple<List<Statement>, Set<IProgramVar>, IcfgLocation> constructTransitionStatements(IcfgEdge edge) {
		final List<Statement> statements = new ArrayList<>();
		final Set<IProgramVar> vars = new HashSet<>();
		addStatementsAndVariables(edge, statements, vars);
		while (isBridgingLocation(edge.getTarget())) {
			edge = edge.getTarget().getOutgoingEdges().get(0);
			addStatementsAndVariables(edge, statements, vars);
		}
		final String targetLabel = constructLabelId(edge.getTarget());
		statements.add(new GotoStatement(constructNewLocation(), new String[] { targetLabel }));
		return new Triple<>(statements, vars, edge.getTarget());
	}

	private void addStatementsAndVariables(final IcfgEdge edge, final List<Statement> statements,
			final Set<IProgramVar> vars) {
		final StatementSequence stseq = (StatementSequence) edge.getLabel();
		vars.addAll(stseq.getTransformula().getInVars().keySet());
		vars.addAll(stseq.getTransformula().getOutVars().keySet());
		for (final Statement st : stseq.getStatements()) {
			statements.add(st);
		}
	}
	
	/**
	 * @return true iff location has exactly one outgoing edge and one incoming edge
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
