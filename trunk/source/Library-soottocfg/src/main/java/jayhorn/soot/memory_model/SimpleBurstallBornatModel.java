/**
 * 
 */
package jayhorn.soot.memory_model;

import java.util.HashMap;
import java.util.Map;

import jayhorn.cfg.Program;
import jayhorn.cfg.Variable;
import jayhorn.cfg.expression.ArrayAccessExpression;
import jayhorn.cfg.expression.ArrayStoreExpression;
import jayhorn.cfg.expression.BinaryExpression;
import jayhorn.cfg.expression.BinaryExpression.BinaryOperator;
import jayhorn.cfg.expression.Expression;
import jayhorn.cfg.expression.IdentifierExpression;
import jayhorn.cfg.expression.InstanceOfExpression;
import jayhorn.cfg.statement.AssignStatement;
import jayhorn.cfg.statement.AssumeStatement;
import jayhorn.cfg.type.IntType;
import jayhorn.cfg.type.Type;
import jayhorn.soot.util.MethodInfo;
import jayhorn.soot.util.SootTranslationHelpers;
import soot.SootField;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.DoubleConstant;
import soot.jimple.FloatConstant;
import soot.jimple.InstanceFieldRef;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StringConstant;

/**
 * @author schaef
 *
 */
public class SimpleBurstallBornatModel extends MemoryModel {

	private final Variable nullConstant, heapVariable;
	private Program program;
	private final Map<soot.Type, jayhorn.cfg.type.Type> types = new HashMap<soot.Type, jayhorn.cfg.type.Type>();
	private final Map<SootField, Variable> fieldGlobals = new HashMap<SootField, Variable>();

	public SimpleBurstallBornatModel() {
		this.program = SootTranslationHelpers.v().getProgram();
		// TODO
		this.nullConstant = this.program.loopupGlobalVariable("$null", null);
		this.heapVariable = this.program.loopupGlobalVariable("$heap", null);
	}

	@Override
	public void mkHeapAssignment(Unit u, Value lhs, Value rhs) {
		rhs.apply(valueSwitch);
		Expression value = valueSwitch.popExpression();
		Expression target;
		Expression[] indices;
		if (lhs instanceof InstanceFieldRef) {
			InstanceFieldRef ifr = (InstanceFieldRef) lhs;
			ifr.getBase().apply(valueSwitch);
			Expression base = valueSwitch.popExpression();
			// TODO: assert that base!=null
			Variable fieldVar = lookupField(ifr.getField());
			indices = new Expression[] { base,
					new IdentifierExpression(fieldVar) };
			target = new IdentifierExpression(this.heapVariable);
		} else if (lhs instanceof ArrayRef) {
			ArrayRef ar = (ArrayRef) lhs;
			ar.getBase().apply(valueSwitch);
			Expression base = valueSwitch.popExpression();
			// TODO: assert that idx is in bounds.
			ar.getIndex().apply(valueSwitch);
			Expression arrayIdx = valueSwitch.popExpression();
			indices = new Expression[] { base, arrayIdx };
			target = new IdentifierExpression(this.heapVariable);
			// TODO: only a hack.
		} else {
			throw new RuntimeException();
		}
		this.statementSwitch.push(new AssignStatement(SootTranslationHelpers.v().getSourceLocation(u),
				new IdentifierExpression(heapVariable),
				new ArrayStoreExpression(target, indices, value)));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see jayhorn.soot.memory_model.MemoryModel#mkNewExpr(soot.jimple.NewExpr)
	 */
	@Override
	public Expression mkNewExpr(NewExpr arg0) {
		Type newType = this.lookupType(arg0.getBaseType());
		MethodInfo mi = this.statementSwitch.getMethodInto();
		Variable newLocal = mi.createFreshLocal("$new", newType);
		// add: assume newLocal!=null
		this.statementSwitch.push(new AssumeStatement(SootTranslationHelpers.v().getSourceLocation(this.statementSwitch
				.getCurrentStmt()), new BinaryExpression(BinaryOperator.Ne,
				new IdentifierExpression(newLocal), this.mkNullConstant())));
		// add: assume newLocal instanceof newType
		this.statementSwitch.push(new AssumeStatement(SootTranslationHelpers.v().getSourceLocation(this.statementSwitch
				.getCurrentStmt()), new InstanceOfExpression(
				new IdentifierExpression(newLocal), SootTranslationHelpers.v()
						.lookupTypeVariable(arg0.getBaseType()))));

		return new IdentifierExpression(newLocal);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * jayhorn.soot.memory_model.MemoryModel#mkNewArrayExpr(soot.jimple.NewArrayExpr
	 * )
	 */
	@Override
	public Expression mkNewArrayExpr(NewArrayExpr arg0) {
		// TODO Auto-generated method stub		
		return new IdentifierExpression(SootTranslationHelpers.v().getProgram().loopupGlobalVariable("TODO", IntType.instance()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * jayhorn.soot.memory_model.MemoryModel#mkNewMultiArrayExpr(soot.jimple
	 * .NewMultiArrayExpr)
	 */
	@Override
	public Expression mkNewMultiArrayExpr(NewMultiArrayExpr arg0) {
		// TODO Auto-generated method stub
		return new IdentifierExpression(SootTranslationHelpers.v().getProgram().loopupGlobalVariable("TODO", IntType.instance()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * jayhorn.soot.memory_model.MemoryModel#mkArrayRefExpr(soot.jimple.ArrayRef
	 * )
	 */
	@Override
	public Expression mkArrayRefExpr(ArrayRef arg0) {
		// TODO Auto-generated method stub
		return new IdentifierExpression(SootTranslationHelpers.v().getProgram().loopupGlobalVariable("TODO", IntType.instance()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see jayhorn.soot.memory_model.MemoryModel#mkArrayLengthExpr(soot.Value)
	 */
	@Override
	public Expression mkArrayLengthExpr(Value arg0) {
		// TODO Auto-generated method stub
		return new IdentifierExpression(SootTranslationHelpers.v().getProgram().loopupGlobalVariable("TODO", IntType.instance()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see jayhorn.soot.memory_model.MemoryModel#mkStringLengthExpr(soot.Value)
	 */
	@Override
	public Expression mkStringLengthExpr(Value arg0) {
		// TODO Auto-generated method stub
		return new IdentifierExpression(SootTranslationHelpers.v().getProgram().loopupGlobalVariable("TODO", IntType.instance()));
	}
	
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * jayhorn.soot.memory_model.MemoryModel#mkInstanceFieldRefExpr(soot.jimple
	 * .InstanceFieldRef)
	 */
	@Override
	public Expression mkInstanceFieldRefExpr(InstanceFieldRef arg0) {
		arg0.getBase().apply(valueSwitch);
		Expression base = valueSwitch.popExpression();
		Variable fieldVar = lookupField(arg0.getField());
		// TODO call the error model.
		return new ArrayAccessExpression(new IdentifierExpression(
				this.heapVariable), new Expression[] { base,
				new IdentifierExpression(fieldVar) });
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * jayhorn.soot.memory_model.MemoryModel#mkStaticFieldRefExpr(soot.jimple
	 * .StaticFieldRef)
	 */
	@Override
	public Expression mkStaticFieldRefExpr(StaticFieldRef arg0) {
		return new IdentifierExpression(lookupField(arg0.getField()));
	}

	private Variable lookupField(SootField field) {
		if (!this.fieldGlobals.containsKey(field)) {
			final String fieldName = field.getDeclaringClass().getName() + "."
					+ field.getName();
			Variable fieldVar = this.program.loopupGlobalVariable(fieldName,
					this.lookupType(field.getType()));
			this.fieldGlobals.put(field, fieldVar);
		}
		return this.fieldGlobals.get(field);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see jayhorn.soot.memory_model.MemoryModel#mkNullConstant()
	 */
	@Override
	public Expression mkNullConstant() {
		return new IdentifierExpression(nullConstant);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see jayhorn.soot.memory_model.MemoryModel#mkStringConstant(soot.jimple.
	 * StringConstant)
	 */
	@Override
	public Expression mkStringConstant(StringConstant arg0) {
		// TODO Auto-generated method stub
		return new IdentifierExpression(SootTranslationHelpers.v().getProgram().loopupGlobalVariable("TODO", IntType.instance()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see jayhorn.soot.memory_model.MemoryModel#mkDoubleConstant(soot.jimple.
	 * DoubleConstant)
	 */
	@Override
	public Expression mkDoubleConstant(DoubleConstant arg0) {
		// TODO Auto-generated method stub
		return new IdentifierExpression(SootTranslationHelpers.v().getProgram().loopupGlobalVariable("TODO", IntType.instance()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see jayhorn.soot.memory_model.MemoryModel#mkFloatConstant(soot.jimple.
	 * FloatConstant)
	 */
	@Override
	public Expression mkFloatConstant(FloatConstant arg0) {
		// TODO Auto-generated method stub
		return new IdentifierExpression(SootTranslationHelpers.v().getProgram().loopupGlobalVariable("TODO", IntType.instance()));
	}

	@Override
	public Type lookupType(soot.Type t) {
		if (!types.containsKey(t)) {
			// TODO:
		}
		return types.get(t);
	}

}
