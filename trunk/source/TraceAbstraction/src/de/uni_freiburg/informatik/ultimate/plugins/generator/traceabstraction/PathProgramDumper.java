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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogieOutput;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.TypeSortTranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
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

	public enum InputMode {
		BOOGIE, ICFG
	}

	private final InputMode mInputMode;
	private final boolean FILTER_VARIABLES_OF_BOOGIE_INPUT = false;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final ConstructionCache.IValueConstruction<IcfgLocation, String> mLoc2LabelVC =
			new ConstructionCache.IValueConstruction<IcfgLocation, String>() {

		private int mCounter = 0;

		@Override
		public String constructValue(final IcfgLocation key) {
			final String result = "loc" + String.valueOf(mCounter);
			mCounter++;
			return result;
		}

	};
	private final ConstructionCache<IcfgLocation, String> mLoc2LabelId = new ConstructionCache<>(mLoc2LabelVC);
	private final PathProgram mPathProgram;
	private final IIcfg<?> mOriginalIcfg;
	private final Term2Expression mTerm2Expression;
	private final TypeSortTranslator mTypeSortTranslator;

	private enum Program {
		PATH_PROGRAM, ORIGINAL_PROGRAM
	}

	public PathProgramDumper(final IIcfg<?> icfg, final IUltimateServiceProvider services,
			final NestedRun<? extends IAction, IPredicate> run, final String filename, final InputMode inputMode) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mOriginalIcfg = icfg;
		mInputMode = inputMode;
		if (mInputMode == InputMode.BOOGIE) {
			if (!(icfg instanceof BoogieIcfgContainer)) {
				throw new UnsupportedOperationException("PathProgramDumper currently needs BoogieIcfgContainer");
			}
			mTerm2Expression = null;
			mTypeSortTranslator = ((BoogieIcfgContainer) icfg).getBoogie2SMT().getTypeSortTranslator();
		} else {
			final TypeSortTranslator tsTranslation =
					constructFakeTypeSortTranslator(icfg.getCfgSmtToolkit().getManagedScript());
			final Unit unit = new Unit(constructNewLocation(), new Declaration[0]);
			final BoogieDeclarations boogieDeclarations = new BoogieDeclarations(unit, mLogger);
			final Boogie2SmtSymbolTable boogie2SmtSymbolTable =
					new FakeBoogie2SmtSymbolTable(icfg.getCfgSmtToolkit().getManagedScript(), tsTranslation,
							icfg.getCfgSmtToolkit().getSymbolTable(), boogieDeclarations);
			mTerm2Expression = new Term2Expression(tsTranslation, boogie2SmtSymbolTable,
					icfg.getCfgSmtToolkit().getManagedScript());
			mTypeSortTranslator =
					new TypeSortTranslator(icfg.getCfgSmtToolkit().getManagedScript().getScript(), services);
		}

		final Set<? extends IcfgEdge> allowedTransitions = extractTransitionsFromRun(run.getWord());
		final PathProgram.PathProgramConstructionResult ppResult =
				PathProgram.constructPathProgram("PathInvariantsPathProgram", icfg, allowedTransitions);
		mPathProgram = ppResult.getPathProgram();

		final List<Declaration> newDeclarations = new ArrayList<>();
		final Set<IProgramVar> globalVars = new HashSet<>();
		for (final Entry<String, IcfgLocation> entry : mPathProgram.getProcedureEntryNodes().entrySet()) {
			final Pair<Procedure, Set<IProgramVar>> newImplAndGlobalVars;
			final IcfgLocation exitLoc = mPathProgram.getProcedureExitNodes().get(entry.getKey());
			if (mInputMode == InputMode.BOOGIE) {
				final BoogieIcfgContainer boogieIcfg = (BoogieIcfgContainer) icfg;
				newImplAndGlobalVars = constructNewImplementation(entry.getKey(), entry.getValue(), exitLoc, boogieIcfg,
						mPathProgram.getProcedureErrorNodes().get(entry.getKey()));
			} else {
				newImplAndGlobalVars = constructNewImplementation(entry.getKey(), entry.getValue(), exitLoc,
						mPathProgram.getProcedureErrorNodes().get(entry.getKey()));
			}

			newDeclarations.add(newImplAndGlobalVars.getFirst());
			globalVars.addAll(newImplAndGlobalVars.getSecond());

			if (mInputMode == InputMode.BOOGIE) {
				final BoogieIcfgContainer boogieIcfg = (BoogieIcfgContainer) icfg;
				final Procedure spec = boogieIcfg.getBoogieDeclarations().getProcSpecification().get(entry.getKey());
				final Procedure impl = boogieIcfg.getBoogieDeclarations().getProcImplementation().get(entry.getKey());
				if (spec != impl) {
					newDeclarations.add(spec);
				}
			}
		}

		if (mInputMode == InputMode.BOOGIE) {
			final BoogieIcfgContainer boogieIcfg = (BoogieIcfgContainer) icfg;
			for (final Entry<String, Procedure> entry : boogieIcfg.getBoogieDeclarations().getProcSpecification()
					.entrySet()) {
				if (entry.getValue().getBody() == null
						&& !boogieIcfg.getProcedureEntryNodes().containsKey(entry.getKey())) {
					// is specification without implementation
					newDeclarations.add(entry.getValue());
				}
			}
			if (FILTER_VARIABLES_OF_BOOGIE_INPUT) {
				newDeclarations.addAll(0,
						Arrays.asList(filter(boogieIcfg.getBoogieDeclarations().getGlobalVarDeclarations(),
								extractIdentifiers(globalVars))));
			} else {
				newDeclarations.addAll(0, boogieIcfg.getBoogieDeclarations().getGlobalVarDeclarations());
			}
			newDeclarations.addAll(0, boogieIcfg.getBoogieDeclarations().getFunctionDeclarations());
			newDeclarations.addAll(0, boogieIcfg.getBoogieDeclarations().getAxioms());
			newDeclarations.addAll(0, boogieIcfg.getBoogieDeclarations().getConstDeclarations());
			newDeclarations.addAll(0, boogieIcfg.getBoogieDeclarations().getTypeDeclarations());
		} else {
			newDeclarations.addAll(0, Arrays.asList(constructDeclarations(globalVars)));
		}

		final Unit unit =
				new Unit(constructNewLocation(), newDeclarations.toArray(new Declaration[newDeclarations.size()]));

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

	private TypeSortTranslator constructFakeTypeSortTranslator(final ManagedScript managedScript) {
		final TypeSortTranslator result =
				new TypeSortTranslator(Collections.emptySet(), managedScript.getScript(), mServices);
		final IBoogieType type = BoogieType.TYPE_INT;
		final BoogieASTNode astNode = new BoogieASTNode(constructNewLocation());
		result.getSort(type, astNode);
		return result;
	}

	private Pair<Procedure, Set<IProgramVar>> constructNewImplementation(final String proc, final IcfgLocation entryLoc,
			final IcfgLocation exitLoc, final BoogieIcfgContainer boogieIcfg, final Set<IcfgLocation> errorLocs) {
		final Procedure impl = boogieIcfg.getBoogieDeclarations().getProcImplementation().get(proc);
		final Body body = impl.getBody();

		final Triple<List<Statement>, Set<IProgramVar>, Set<IProgramVar>> varsAndNewSt =
				constructProcedureStatements(proc, entryLoc, exitLoc, errorLocs);
		final List<Statement> newStatements = varsAndNewSt.getFirst();

		final VariableDeclaration[] localVars;
		if (FILTER_VARIABLES_OF_BOOGIE_INPUT) {
			localVars = filter(Arrays.asList(body.getLocalVars()), extractIdentifiers(varsAndNewSt.getSecond()));
		} else {
			localVars = body.getLocalVars();
		}
		final Body newBody =
				new Body(constructNewLocation(), localVars, newStatements.toArray(new Statement[newStatements.size()]));
		Specification[] newSpecifications;
		if (impl.getSpecification() == null) {
			newSpecifications = null;
		} else {
			if (FILTER_VARIABLES_OF_BOOGIE_INPUT) {
				newSpecifications = filterModifiesSpecifications(impl.getSpecification(),
						extractIdentifiers(varsAndNewSt.getThird()));
			} else {
				newSpecifications = impl.getSpecification();
			}
		}
		final Procedure newProc = new Procedure(constructNewLocation(), impl.getAttributes(), impl.getIdentifier(),
				impl.getTypeParams(), impl.getInParams(), impl.getOutParams(), newSpecifications, newBody);
		return new Pair<>(newProc, varsAndNewSt.getThird());
	}

	/**
	 * Do construction without boogie program as input.
	 */
	private Pair<Procedure, Set<IProgramVar>> constructNewImplementation(final String proc, final IcfgLocation entryLoc,
			final IcfgLocation exitLoc, final Set<IcfgLocation> errorLocs) {

		final Triple<List<Statement>, Set<IProgramVar>, Set<IProgramVar>> varsAndNewSt =
				constructProcedureStatements(proc, entryLoc, exitLoc, errorLocs);
		final List<Statement> newStatements = varsAndNewSt.getFirst();

		final Set<IProgramVar> localVars = varsAndNewSt.getSecond();
		final VariableDeclaration[] localVarDeclarations = constructDeclarations(localVars);
		final Body newBody = new Body(constructNewLocation(), localVarDeclarations,
				newStatements.toArray(new Statement[newStatements.size()]));
		final Attribute[] attributes = new Attribute[0];
		final String identifier = entryLoc.getProcedure();
		final String[] typeParams = new String[0];
		final VarList[] inParams = new VarList[0];
		final VarList[] outParams = new VarList[0];
		ModifiesSpecification modifiesSpecification;
		{
			final VariableLHS[] identifiers = new VariableLHS[varsAndNewSt.getThird().size()];
			int offset = 0;
			for (final IProgramVar pv : varsAndNewSt.getThird()) {
				identifiers[offset] = new VariableLHS(constructNewLocation(), translateIdentifier(pv));
				offset++;
			}
			modifiesSpecification = new ModifiesSpecification(constructNewLocation(), false, identifiers);
		}
		final Specification[] specification = new Specification[] { modifiesSpecification };
		final Procedure newProc = new Procedure(constructNewLocation(), attributes, identifier, typeParams, inParams,
				outParams, specification, newBody);
		return new Pair<>(newProc, varsAndNewSt.getThird());
	}

	private VariableDeclaration[] constructDeclarations(final Set<IProgramVar> localVars) {
		final VariableDeclaration[] result = new VariableDeclaration[localVars.size()];
		int offset = 0;
		for (final IProgramVar pv : localVars) {
			// assert (pv instanceof ILocalProgramVar) : "not a local var";
			final IdentifierExpression id = translateVar(pv);
			final Attribute[] attributes = new Attribute[0];
			final String[] identifiers = new String[] { id.getIdentifier() };
			final ASTType astType;
			if (mInputMode == InputMode.BOOGIE) {
				// FIXME: do not only support int.
				String typeName;
				if (SmtSortUtils.isIntSort(pv.getTermVariable().getSort())) {
					typeName = "int";
				} else if (SmtSortUtils.isBoolSort(pv.getTermVariable().getSort())) {
					typeName = "bool";
				} else {
					throw new UnsupportedOperationException(
							"Translation does not support sort " + pv.getTermVariable().getSort().getName());
				}
				astType = new PrimitiveType(constructNewLocation(), typeName);
			} else {
				final BoogieType boogieType = (BoogieType) mTypeSortTranslator.getType(pv.getTermVariable().getSort());
				astType = boogieType.toASTType(constructNewLocation());
			}

			final VarList varList = new VarList(constructNewLocation(), identifiers, astType);
			final VarList[] variables = new VarList[] { varList };
			result[offset] = new VariableDeclaration(constructNewLocation(), attributes, variables);
			offset++;
		}
		return result;
	}

	private String translateIdentifier(final IProgramVar pv) {
		final String result = ((IdentifierExpression) mTerm2Expression.translate(pv.getTermVariable())).getIdentifier();
		if (result == null) {
			throw new AssertionError("unable to translate " + pv);
		}
		return result;
	}

	private IdentifierExpression translateVar(final IProgramVar pv) {
		final IdentifierExpression result = ((IdentifierExpression) mTerm2Expression.translate(pv.getTermVariable()));
		if (result == null) {
			throw new AssertionError("unable to translateI " + pv);
		}
		return result;
	}

	private static Specification[] filterModifiesSpecifications(final Specification[] specification,
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

	private static ModifiesSpecification filter(final ModifiesSpecification modSpec, final Set<String> globalVars) {
		final List<VariableLHS> filteredIdentifiers = new ArrayList<>();
		for (final VariableLHS varLhs : modSpec.getIdentifiers()) {
			if (globalVars.contains(varLhs.getIdentifier())) {
				filteredIdentifiers.add(varLhs);
			}
		}
		return new ModifiesSpecification(modSpec.getLocation(), modSpec.isFree(),
				filteredIdentifiers.toArray(new VariableLHS[filteredIdentifiers.size()]));
	}

	private static Set<String> extractIdentifiers(final Set<IProgramVar> vars) {
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

	private static VariableDeclaration[] filter(final List<VariableDeclaration> localVars, final Set<String> vars) {
		final List<VariableDeclaration> result = new ArrayList<>();
		for (final VariableDeclaration varDecl : localVars) {
			final VariableDeclaration newDecl = filter(varDecl, vars);
			if (newDecl != null) {
				result.add(newDecl);
			}
		}
		return result.toArray(new VariableDeclaration[result.size()]);
	}

	private static VariableDeclaration filter(final VariableDeclaration varDecl, final Set<String> vars) {
		final List<VarList> resultVarLists = new ArrayList<>();
		for (final VarList varList : varDecl.getVariables()) {
			final String[] newIdentifiers = filter(varList.getIdentifiers(), vars);
			if (newIdentifiers.length > 0) {
				resultVarLists.add(new VarList(varList.getLocation(), newIdentifiers, varList.getType()));
			}
		}
		if (resultVarLists.isEmpty()) {
			return null;
		}
		return new VariableDeclaration(varDecl.getLocation(), new Attribute[0],
				resultVarLists.toArray(new VarList[resultVarLists.size()]));
	}

	private static String[] filter(final String[] identifiers, final Set<String> vars) {
		final Predicate<? super String> pred = (x -> vars.contains(x));
		return Arrays.stream(identifiers).filter(pred).toArray(size -> new String[size]);
	}

	private Triple<List<Statement>, Set<IProgramVar>, Set<IProgramVar>> constructProcedureStatements(final String proc,
			final IcfgLocation initialNode, final IcfgLocation exitNode, final Set<IcfgLocation> errorLocs) {
		final ArrayDeque<IcfgLocation> worklist = new ArrayDeque<>();
		final Set<IcfgLocation> added = new HashSet<>();
		worklist.add(initialNode);
		added.add(initialNode);
		final List<Statement> newStatements = new ArrayList<>();
		final Set<IProgramVar> localVars = new HashSet<>();
		final Set<IProgramVar> globalVars = new HashSet<>();
		while (!worklist.isEmpty()) {
			final IcfgLocation node = worklist.remove();
			if (!node.getProcedure().equals(proc)) {
				throw new AssertionError("added location from different procedure");
			}
			newStatements.add(constructLabel(node));
			if (errorLocs != null && errorLocs.contains(node)) {
				newStatements.add(
						new AssertStatement(constructNewLocation(), new BooleanLiteral(constructNewLocation(), false)));
				assert node.getOutgoingEdges().isEmpty() : "error loc with outgoing transitions";
			}
			final List<IcfgEdge> nonSummaryOutgoingEdges = new ArrayList<>();
			for (final IcfgEdge edge : node.getOutgoingEdges()) {
				if (edge instanceof Summary) {
					if (!((Summary) edge).calledProcedureHasImplementation()) {
						// summaries that do not have an implementation are allowed
						nonSummaryOutgoingEdges.add(edge);
					}
				} else {
					nonSummaryOutgoingEdges.add(edge);
				}
			}
			if (node.getProcedure().equals(proc)) {
				// continue only if we are still in the same procedure
				if (nonSummaryOutgoingEdges.isEmpty()) {
					// do nothing, no successor
				} else if (nonSummaryOutgoingEdges.size() == 1) {
					final IcfgEdge edge = nonSummaryOutgoingEdges.get(0);
					processTransition(worklist, added, newStatements, localVars, globalVars, edge);
				} else {
					final String[] transitionStartLabels = new String[nonSummaryOutgoingEdges.size()];
					for (int i = 0; i < nonSummaryOutgoingEdges.size(); i++) {
						final String transitionStartLabel = constructLabelId(node, i);
						transitionStartLabels[i] = transitionStartLabel;
					}
					if (!nonSummaryOutgoingEdges.isEmpty()) {
						newStatements.add(new GotoStatement(constructNewLocation(), transitionStartLabels));
					}
					for (int i = 0; i < nonSummaryOutgoingEdges.size(); i++) {
						final IcfgEdge edge = nonSummaryOutgoingEdges.get(i);
						if (edge instanceof Summary) {
							// we skip summaries, we obtain the corresponding
							// information via call and return
							// (need it via call and return because we want
							// to see the program variables
							continue;
						}
						newStatements.add(constructLabel(node, i));
						processTransition(worklist, added, newStatements, localVars, globalVars, edge);
					}
				}
			}
		}
		return new Triple<>(newStatements, localVars, globalVars);
	}

	private void processTransition(final ArrayDeque<IcfgLocation> worklist, final Set<IcfgLocation> added,
			final List<Statement> result, final Set<IProgramVar> localvars, final Set<IProgramVar> globalVars,
			final IcfgEdge edge) {
		final Quad<List<Statement>, Set<IProgramVar>, Set<IProgramVar>, IcfgLocation> transResult =
				constructTransitionStatements(edge);
		final String proc = edge.getPrecedingProcedure();
		result.addAll(transResult.getFirst());
		localvars.addAll(transResult.getSecond());
		globalVars.addAll(transResult.getThird());
		if (transResult.getFourth() != null && transResult.getFourth().getProcedure().equals(proc)
				&& !added.contains(transResult.getFourth()) && !isProcedureExit(transResult.getFourth())) {
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

	private Quad<List<Statement>, Set<IProgramVar>, Set<IProgramVar>, IcfgLocation>
	constructTransitionStatements(IcfgEdge edge) {
		final String proc = edge.getPrecedingProcedure();
		final List<Statement> statements = new ArrayList<>();
		final Set<IProgramVar> localVars = new HashSet<>();
		final Set<IProgramVar> globalVars = new HashSet<>();
		IcfgLocation targetLoc;
		targetLoc = addStatementsAndVariables(edge, statements, localVars, globalVars);
		while (targetLoc != null && targetLoc.getProcedure().equals(proc) && isBridgingLocation(targetLoc)
				&& !isProcedureExit(targetLoc)) {
			edge = targetLoc.getOutgoingEdges().get(0);
			targetLoc = addStatementsAndVariables(edge, statements, localVars, globalVars);
		}
		if (targetLoc == null || isProcedureExit(targetLoc)) {
			statements.add(new ReturnStatement(constructNewLocation()));
		} else {
			final String targetLabel = constructLabelId(targetLoc);
			statements.add(new GotoStatement(constructNewLocation(), new String[] { targetLabel }));
		}
		return new Quad<>(statements, localVars, globalVars, targetLoc);
	}

	private boolean isProcedureExit(final IcfgLocation targetLoc) {
		final IcfgLocation exit = mPathProgram.getProcedureExitNodes().get(targetLoc.getProcedure());
		return targetLoc.equals(exit);
	}

	private IcfgLocation addStatementsAndVariables(final IcfgEdge edge, final List<Statement> statements,
			final Set<IProgramVar> localVars, final Set<IProgramVar> globalVars) {
		final IAction action = edge;
		if (mInputMode == InputMode.BOOGIE) {
			if (edge.getLabel() instanceof Call) {
				addVars(action.getTransformula().getInVars().keySet(), localVars, globalVars);
				final IIcfgReturnTransition<?, ?> correspondingReturn =
						getCorrespondingReturn(action, Program.PATH_PROGRAM);
				final CallStatement callStatement = ((Call) edge.getLabel()).getCallStatement();
				statements.add(callStatement);
				if (correspondingReturn == null) {
					// corresponding return not in path program,
					// we take outVars of corresponding return in original
					// program
					final IIcfgReturnTransition<?, ?> correspondingReturnInOriginalProgram =
							getCorrespondingReturn(edge.getLabel(), Program.ORIGINAL_PROGRAM);
					addVars(correspondingReturnInOriginalProgram.getTransformula().getOutVars().keySet(), localVars,
							globalVars);
					return null;
				}
				addVars(correspondingReturn.getTransformula().getOutVars().keySet(), localVars, globalVars);
				return correspondingReturn.getTarget();
			} else if (edge.getLabel() instanceof Return) {
				throw new AssertionError("we should have stopped at procedure exit");
				// addVars(action.getTransformula().getInVars().keySet(),
				// localVars, globalVars);
				// statements.add(new ReturnStatement(constructNewLocation()));
				// return ((Return) action).getTarget();
			} else if (edge.getLabel() instanceof StatementSequence) {
				addVars(action.getTransformula().getInVars().keySet(), localVars, globalVars);
				addVars(action.getTransformula().getOutVars().keySet(), localVars, globalVars);
				final StatementSequence stseq = (StatementSequence) edge.getLabel();
				for (final Statement st : stseq.getStatements()) {
					statements.add(st);
				}
				return edge.getTarget();
			} else if (edge.getLabel() instanceof Summary) {
				addVars(action.getTransformula().getInVars().keySet(), localVars, globalVars);
				addVars(action.getTransformula().getOutVars().keySet(), localVars, globalVars);
				final Summary summary = (Summary) edge.getLabel();
				if (summary.calledProcedureHasImplementation()) {
					throw new AssertionError("edges like this should have been omitted");
				}
				statements.add(summary.getCallStatement());
				return edge.getTarget();
			} else {
				throw new UnsupportedOperationException("unsupported edge " + action.getClass().getSimpleName());
			}
		}
		addVars(action.getTransformula().getInVars().keySet(), localVars, globalVars);
		addVars(action.getTransformula().getOutVars().keySet(), localVars, globalVars);
		final ManagedScript mgdScript = mPathProgram.getCfgSmtToolkit().getManagedScript();
		final UnmodifiableTransFormula guardTf =
				TransFormulaUtils.computeGuard(action.getTransformula(), mgdScript, mServices, mLogger);
		final Term guardTerm = renameInvarsToDefaultVars(mgdScript, guardTf);
		final Expression guardExpression = mTerm2Expression.translate(guardTerm);
		final AssumeStatement assume = new AssumeStatement(constructNewLocation(), guardExpression);

		final SimultaneousUpdate su = new SimultaneousUpdate(action.getTransformula(), mgdScript);
		final AssignmentStatement assignment;
		{
			final LeftHandSide[] lhs = new LeftHandSide[su.getUpdatedVars().size()];
			final Expression[] rhs = new Expression[su.getUpdatedVars().size()];
			int offset = 0;
			for (final Entry<IProgramVar, Term> entry : su.getUpdatedVars().entrySet()) {
				lhs[offset] = new VariableLHS(constructNewLocation(),
						((IdentifierExpression) mTerm2Expression.translate(entry.getKey().getTermVariable()))
						.getIdentifier());
				rhs[offset] = mTerm2Expression.translate(entry.getValue());
				offset++;
			}
			assignment = new AssignmentStatement(constructNewLocation(), lhs, rhs);
		}

		final HavocStatement havoc;
		{
			final VariableLHS[] identifiers = new VariableLHS[su.getHavocedVars().size()];
			int offset = 0;
			for (final IProgramVar pv : su.getHavocedVars()) {
				identifiers[offset] = new VariableLHS(constructNewLocation(), translateIdentifier(pv));
				offset++;
			}
			havoc = new HavocStatement(constructNewLocation(), identifiers);
		}
		if (!SmtUtils.isTrueLiteral(guardTerm)) {
			statements.add(assume);
		}
		if (!su.getUpdatedVars().isEmpty()) {
			statements.add(assignment);
		}
		if (!su.getHavocedVars().isEmpty()) {
			statements.add(havoc);
		}
		return edge.getTarget();

	}

	private Term renameInvarsToDefaultVars(final ManagedScript mgdScript, final UnmodifiableTransFormula guardTf) {
		final boolean eachFreeVarIsInvar = TransFormulaUtils.eachFreeVarIsInvar(guardTf, guardTf.getFormula());
		if (!eachFreeVarIsInvar) {
			throw new IllegalArgumentException("term contains non-Invar");
		}
		final Map<TermVariable, TermVariable> substitutionMapping = TransFormulaUtils
				.constructInvarsToDefaultvarsMap(guardTf);
		return new Substitution(mgdScript, substitutionMapping).transform(guardTf.getFormula());
	}



	private IIcfgReturnTransition<?, ?> getCorrespondingReturn(final IAction action, final Program program) {
		IIcfgReturnTransition<?, ?> correspondingReturn = null;
		final IcfgLocation exitLoc;
		switch (program) {
		case ORIGINAL_PROGRAM:
			exitLoc = mOriginalIcfg.getProcedureExitNodes().get(action.getSucceedingProcedure());
			break;
		case PATH_PROGRAM:
			exitLoc = mPathProgram.getProcedureExitNodes().get(action.getSucceedingProcedure());
			break;
		default:
			throw new AssertionError("unknown value " + program);
		}
		if (exitLoc == null) {
			// corresponding return not in path program
			return null;
		}
		for (final IcfgEdge returnEdge : exitLoc.getOutgoingEdges()) {
			final IIcfgReturnTransition<?, ?> ret = (IIcfgReturnTransition<?, ?>) returnEdge;
			if (ret.getCorrespondingCall().equals(action)) {
				if (correspondingReturn == null) {
					correspondingReturn = ret;
				} else {
					throw new AssertionError("several corresponding returns");
				}
			}
		}
		if (correspondingReturn == null) {
			throw new AssertionError("no corresponding return");
		}
		return correspondingReturn;
	}

	/**
	 * Given a set of {@link IProgramVar}, sort them into localVars and globalVars.
	 */
	private static void addVars(final Set<IProgramVar> vars, final Set<IProgramVar> localVars,
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
	 * @return true iff location has exactly one outgoing edge and one incoming edge
	 */
	private static boolean isBridgingLocation(final IcfgLocation loc) {
		return loc.getIncomingEdges().size() == 1 && loc.getOutgoingEdges().size() == 1;
	}

	private static ILocation constructNewLocation() {
		return new DefaultLocation();
	}

	private static Set<? extends IcfgEdge> extractTransitionsFromRun(final NestedWord<? extends IAction> word) {
		final Set<IcfgEdge> result = new HashSet<>();
		for (final IAction letter : word) {
			final IcfgEdge edge = (IcfgEdge) letter;
			result.add(edge);
		}
		return result;
	}

	private static final class FakeBoogie2SmtSymbolTable extends Boogie2SmtSymbolTable {

		private final IIcfgSymbolTable mIIcfgSymbolTable;

		public FakeBoogie2SmtSymbolTable(final ManagedScript script, final TypeSortTranslator typeSortTranslator,
				final IIcfgSymbolTable symbolTable, final BoogieDeclarations boogieDeclarations) {
			super(boogieDeclarations, script, typeSortTranslator);
			mIIcfgSymbolTable = symbolTable;
		}

		@Override
		public IProgramVar getProgramVar(final TermVariable tv) {
			return mIIcfgSymbolTable.getProgramVar(tv);
		}

		@Override
		public BoogieASTNode getAstNode(final IProgramVar bv) {
			return new BoogieASTNode(constructNewLocation());
		}

	}

}
