package de.uni_freiburg.informatik.ultimate.source.java;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;
import org.joogie.boogie.BoogieAxiom;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieType;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

//TODO: Pull line numbers from soot statements to the top; extend location tag for this 

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class Joogie2BoogieTranslator {

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;
	private final Unit mOutput;
	private final BoogieLocation mLoc;
	private final BoogieLocation mLoopLoc;
	private final String mFilename;

	public Joogie2BoogieTranslator(final BoogieProgram program, final IUltimateServiceProvider services,
			final String filename) {
		if (program == null) {
			throw new IllegalArgumentException("program");
		}

		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mFilename = filename;
		mLoc = new BoogieLocation(filename, -1, -1, -1, -1, false);
		mLoopLoc = new BoogieLocation(filename, -1, -1, -1, -1, true);

		mOutput = translate(program);
	}

	public Unit getUnit() {
		return mOutput;
	}

	private Unit translate(final BoogieProgram program) {
		mLogger.info("Translating " + mFilename + " to Ultimate's data structures");
		final List<Declaration> decls = new ArrayList<>();

		decls.addAll(declarePrelude(program));
		decls.addAll(declareConstants(program));
		decls.addAll(declareVariables(program));
		decls.addAll(declareProcedures(program));

		return new Unit(getLocation(), decls.toArray(new Declaration[decls.size()]));
	}

	/**
	 * Note that we generate the Joogie legacy prelude here and that we only
	 * support the Default heap mode
	 */
	private Collection<? extends Declaration> declarePrelude(final BoogieProgram program) {
		final List<Declaration> decls = new ArrayList<>();

		decls.add(new TypeDeclaration(getLocation(), null, false, BoogieBaseTypes.getRefArrType().getName(), null));
		decls.add(new TypeDeclaration(getLocation(), null, false, BoogieBaseTypes.getRealType().getName(), null));
		decls.add(new TypeDeclaration(getLocation(), null, false, BoogieBaseTypes.getClassConstType().getName(), null));
		decls.add(new TypeDeclaration(getLocation(), null, false, "Field", new String[] { "x" }));
		decls.add(declareVariable(program.getHeapVariable()));

		decls.add(declareConstant(program.getNullReference()));

		decls.add(declareConstant(program.getNullIntArray()));
		decls.add(declareConstant(program.getNullRealArray()));
		decls.add(declareConstant(program.getNullRefArray()));

		decls.add(declareConstant(program.getSizeIndexArray()));

		decls.add(declareVariable(program.getSizeArrayInt()));
		decls.add(declareVariable(program.getSizeArrayReal()));
		decls.add(declareVariable(program.getSizeArrayRef()));

		decls.add(declareVariable(program.getSizeString()));

		for (final BoogieAxiom axiom : program.getAxioms()) {
			decls.add(declareAxiom(axiom));
		}

		return decls;
	}

	private Collection<? extends Declaration> declareProcedures(final BoogieProgram program) {
		final List<Declaration> decls = new ArrayList<>();
		program.getProcedures().stream().filter(p -> !isFunction(p)).forEach(p -> decls.addAll(declareProcedure(p)));
		program.getProcedures().stream().filter(p -> isFunction(p)).forEach(p -> decls.addAll(declareFunction(p)));
		return decls;
	}

	private Collection<? extends Declaration> declareVariables(final BoogieProgram program) {
		final List<Declaration> decls = new ArrayList<>();
		program.getGlobalVariables().stream().filter(g -> !g.isConstUnique())
				.forEach(g -> decls.add(declareVariable(g)));
		return decls;
	}

	private Collection<? extends Declaration> declareConstants(final BoogieProgram program) {
		final List<Declaration> decls = new ArrayList<>();

		// first, type constants
		for (Variable typeVar : program.getTypeVariables()) {
			decls.add(declareConstant(typeVar));
		}

		program.getGlobalVariables().stream().filter(g -> g.isConstUnique())
				.forEach(g -> decls.add(declareConstant(g)));

		return decls;
	}

	private ILocation getLoopLocation() {
		return mLoopLoc;
	}

	private ILocation getLocation() {
		return mLoc;
	}

	private Collection<Procedure> declareProcedure(BoogieProcedure proc) {
		// Note that in Joogie, procedures can be functions as well as
		// procedures
		assert!isFunction(proc);

		return null;
	}

	private Collection<Declaration> declareFunction(BoogieProcedure proc) {
		assert isFunction(proc);

		final List<Declaration> decls = new ArrayList<>();
		decls.add(declareFunctionProcedure(proc));

		return decls;
	}

	private Declaration declareFunctionProcedure(BoogieProcedure proc) {
		assert isFunction(proc);

		final Collection<VarList> inParams = new ArrayList<>();
		if (!proc.isStatic()) {
			inParams.add(makeVarList(proc.getThisVariable()));
		}
		proc.getParameterList().stream().map(p -> makeVarList(p)).forEach(inParams::add);

		final VarList outParam;
		if (proc.getReturnVariable() == null && proc.getExceptionalReturnVariables().size() == 0) {
			outParam = null;
		} else {
			final Collection<String> identifiers = new ArrayList<String>();
			ASTType type = null;
			if (proc.getReturnVariable() != null) {
				identifiers.add(proc.getReturnVariable().getName());
				type = Joogie2BoogieUtil.getASTType(proc.getReturnVariable(), mLoc);
			}

			for (final Entry<BoogieType, org.joogie.boogie.expressions.Expression> entry : proc
					.getExceptionalReturnVariables().entrySet()) {
				identifiers.add(((Variable) entry.getValue()).getName());
				type = Joogie2BoogieUtil.getASTType(entry.getKey(), mLoc);
			}
			assert type != null;
			outParam = new VarList(mLoc, identifiers.toArray(new String[identifiers.size()]), type);
		}

		return new FunctionDeclaration(mLoc, null, proc.getName(), null, inParams.toArray(new VarList[inParams.size()]),
				outParam);
	}

	private boolean isFunction(BoogieProcedure proc) {
		return proc.isPure() && returnsOnlyOneType(proc);
	}

	private boolean returnsOnlyOneType(BoogieProcedure proc) {
		final Set<BoogieType> set = new HashSet<BoogieType>();
		if (proc.getReturnVariable() != null) {
			set.add(proc.getReturnVariable().getType());
		}
		if (proc.getExceptionalReturnVariables() != null) {
			proc.getExceptionalReturnVariables().entrySet().stream().forEach(a -> set.add(a.getKey()));
		}
		return set.size() < 2;
	}

	private Declaration declareAxiom(BoogieAxiom axiom) {
		return new Axiom(getLocation(), null, makeExpression(axiom.getExpression()));
	}

	private Expression makeExpression(org.joogie.boogie.expressions.Expression expression) {
		return new ExpressionTranslator(mLogger, getLocation(), expression).getTranslation();
	}

	private VariableDeclaration declareVariable(Variable var) {
		return new VariableDeclaration(getLocation(), null, new VarList[] { makeVarList(var) });
	}

	private ConstDeclaration declareConstant(Variable var) {
		return new ConstDeclaration(getLocation(), null, var.isConstUnique(), makeVarList(var), null, true);
	}

	private VarList makeVarList(Variable var) {
		return new VarList(getLocation(), new String[] { var.getName() }, Joogie2BoogieUtil.getASTType(var, mLoc));
	}

}
