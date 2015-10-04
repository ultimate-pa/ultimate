package de.uni_freiburg.informatik.ultimate.source.java.soottocfg;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.source.java.Activator;
import soottocfg.cfg.Program;
import soottocfg.cfg.Variable;
import soottocfg.cfg.method.CfgBlock;
import soottocfg.cfg.method.Method;
import soottocfg.cfg.statement.CallStatement;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class SootToCfg2BoogieTranslator {

	private final Logger mLogger;
	private final Unit mUnit;
	private final BoogieLocation mLoc;
	private final BoogieLocation mLoopLoc;

	public SootToCfg2BoogieTranslator(final Program prog, final IUltimateServiceProvider services,
			final String filename) {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);

		// FIXME: we need locations from soottocfg but so far we dont have any.
		// So we use a dummy location for everything
		mLoc = new BoogieLocation(filename, -1, -1, -1, -1, false);
		mLoopLoc = new BoogieLocation(filename, -1, -1, -1, -1, true);

		mUnit = translate(prog, filename);
	}

	public Unit getUnit() {
		return mUnit;
	}

	private Unit translate(final Program program, final String filename) {
		mLogger.info("Translating " + filename + " to Ultimate's data structures");
		final List<Declaration> decls = new ArrayList<>();

		decls.addAll(declarePrelude(program));
		decls.addAll(declareConstants(program));
		decls.addAll(declareVariables(program));
		decls.addAll(declareProcedures(program));

		return new Unit(mLoc, decls.toArray(new Declaration[decls.size()]));
	}

	private Collection<? extends Declaration> declareProcedures(final Program program) {
		final Collection<Declaration> rtr = new ArrayList<Declaration>();
		final Set<Method> closed = new HashSet<Method>();
		final ArrayDeque<Method> worklist = new ArrayDeque<>();
		worklist.addAll(Arrays.asList(program.getEntryPoints()));

		while (!worklist.isEmpty()) {
			final Method current = worklist.removeFirst();
			if (!closed.add(current)) {
				continue;
			}
			rtr.add(declareProcedure(program, current, worklist));
		}

		return rtr;
	}

	private Declaration declareProcedure(final Program program, final Method current,
			final ArrayDeque<Method> worklist) {
		final VarList[] inParams = declareInParams(program, current);
		final VarList[] outParams = declareOutParams(program, current);
		final Specification[] specification = declareSpecifications(program, current);
		final Body body = declareBody(program, current, worklist);
		return new Procedure(mLoc, new Attribute[0], current.getMethodName(), new String[0], inParams, outParams,
				specification, body);
	}

	private Body declareBody(final Program program, final Method current, final ArrayDeque<Method> worklist) {
		final VariableDeclaration[] localVars = declareLocalVars(program, current);
		final Statement[] block = declareStatements(program, current, worklist);
		return new Body(mLoc, localVars, block);
	}

	private Statement[] declareStatements(final Program program, final Method method,
			final ArrayDeque<Method> callWorklist) {
		final Collection<Statement> rtr = new ArrayList<Statement>();
		final ArrayDeque<CfgBlock> worklist = new ArrayDeque<>();
		final Set<CfgBlock> closed = new HashSet<>();
		worklist.add(method.getSource());

		while (!worklist.isEmpty()) {
			final CfgBlock current = worklist.removeFirst();
			closed.add(current);

			rtr.add(new Label(mLoc, current.getLabel()));
			rtr.addAll(declareStatements(current, callWorklist));
			final List<CfgBlock> succs = current.getSuccessors();
			if (succs.isEmpty()) {
				rtr.add(new ReturnStatement(mLoc));
			} else {
				final String[] succLabels = succs.stream().map(s -> s.getLabel()).collect(Collectors.toList())
						.toArray(new String[0]);
				rtr.add(new GotoStatement(mLoc, succLabels));
				succs.stream().filter(s -> !closed.contains(s)).forEach(worklist::add);
			}
		}

		return rtr.toArray(new Statement[rtr.size()]);
	}

	private Collection<? extends Statement> declareStatements(final CfgBlock current,
			final ArrayDeque<Method> callWorklist) {
		final Collection<Statement> rtr = new ArrayList<Statement>();
		for (soottocfg.cfg.statement.Statement stmt : current.getStatements()) {
			rtr.add(SootToCfgStatementTranslator.translate(mLogger,
					new BoogieLocation(mLoc.getFileName(), stmt.getJavaSourceLine(), -1, -1, -1, false), stmt));
			if (stmt instanceof CallStatement) {
				callWorklist.addFirst(((CallStatement) stmt).getCallTarget());
			}
		}
		return rtr;
	}

	private VariableDeclaration[] declareLocalVars(final Program program, final Method current) {
		return new VariableDeclaration[] {
				new VariableDeclaration(mLoc, new Attribute[0], makeVarLists(current.getLocals())) };
	}

	private Specification[] declareSpecifications(final Program program, final Method current) {
		final Collection<Specification> rtr = new ArrayList<Specification>();
		final Collection<Variable> modifies = current.getModifiedGlobals();
		if (!modifies.isEmpty()) {
			final List<VariableLHS> vlhs = modifies.stream().map(var -> new VariableLHS(mLoc, var.getName()))
					.collect(Collectors.toList());
			rtr.add(new ModifiesSpecification(mLoc, false, vlhs.toArray(new VariableLHS[vlhs.size()])));
		}

		return rtr.toArray(new Specification[rtr.size()]);
	}

	private VarList[] declareOutParams(final Program program, final Method current) {
		return makeVarLists(current.getOutParams());
	}

	private VarList[] declareInParams(final Program program, final Method current) {
		return makeVarLists(current.getInParams());
	}

	private Collection<? extends Declaration> declareVariables(final Program program) {
		if (program.getGlobalVariables() != null && program.getGlobalVariables().length > 0) {
			return Arrays.asList(program.getGlobalVariables()).stream().map(this::declareVariable)
					.collect(Collectors.toList());
		} else {
			return Collections.emptyList();
		}
	}

	private Collection<? extends Declaration> declareConstants(final Program program) {
		return Collections.emptyList();
	}

	private Collection<? extends Declaration> declarePrelude(final Program program) {
		return Collections.emptyList();
	}

	private VariableDeclaration declareVariable(final Variable var) {
		return new VariableDeclaration(mLoc, new Attribute[0], new VarList[] { makeVarList(var) });
	}

	private ConstDeclaration declareConstant(final Variable var) {
		return new ConstDeclaration(mLoc, new Attribute[0], false, makeVarList(var), null, true);
	}

	private VarList makeVarList(final Variable var) {
		return new VarList(mLoc, new String[] { var.getName() }, SootToCfgTypeTranslator.translate(var, mLoc));
	}

	private VarList[] makeVarLists(final Collection<Variable> vars) {
		return vars.stream().map(p -> makeVarList(p)).collect(Collectors.toList()).toArray(new VarList[0]);
	}

}
