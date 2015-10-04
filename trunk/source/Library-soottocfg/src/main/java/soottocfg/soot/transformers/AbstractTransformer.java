/**
 * 
 */
package soottocfg.soot.transformers;

import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.ThrowStmt;
import soot.tagkit.Host;

/**
 * @author schaef
 *
 */
public abstract class AbstractTransformer extends BodyTransformer {

	/**
	 * 
	 */
	public AbstractTransformer() {
		// TODO Auto-generated constructor stub
	}

	/* (non-Javadoc)
	 * @see soot.BodyTransformer#internalTransform(soot.Body, java.lang.String, java.util.Map)
	 */
	@Override
	protected void internalTransform(Body arg0, String arg1, Map<String, String> arg2) {
		// nothing
	}

	
	protected Unit assignStmtFor(Value left, Value right, Host createdFrom) {
		Unit stmt = Jimple.v().newAssignStmt(left, right);
		stmt.addAllTagsOf(createdFrom);
		return stmt;
	}

	/**
	 * Creates a new jimple IfStmt and adds all tags
	 * from createdFrom to this statement.
	 * @param condition
	 * @param target
	 * @param createdFrom
	 * @return
	 */
	protected Unit ifStmtFor(Value condition, Unit target, Host createdFrom) {
		IfStmt stmt = Jimple.v().newIfStmt(condition, target);
		stmt.addAllTagsOf(createdFrom);
		return stmt;
	}

	/**
	 * Creates a new jimple GotoStmt and adds all tags
	 * from createdFrom to this statement.
	 * @param target
	 * @param createdFrom
	 * @return
	 */
	protected Unit gotoStmtFor(Unit target, Host createdFrom) {
		GotoStmt stmt = Jimple.v().newGotoStmt(target);
		stmt.addAllTagsOf(createdFrom);
		return stmt;
	}

	protected Unit invokeStmtFor(Value ivk, Host createdFrom) {
		InvokeStmt stmt = Jimple.v().newInvokeStmt(ivk);
		stmt.addAllTagsOf(createdFrom);
		return stmt;
	}

	protected Unit throwStmtFor(Value op, Host createdFrom) {
		ThrowStmt stmt = Jimple.v().newThrowStmt(op);
		stmt.addAllTagsOf(createdFrom);
		return stmt;
	}
	
	protected Value jimpleEqZero(Value v) {
		return Jimple.v().newEqExpr(v, IntConstant.v(0));
	}

	protected Value jimpleNeZero(Value v) {
		return Jimple.v().newNeExpr(v, IntConstant.v(0));
	}

	private long counter = 0;

	protected Local getFreshLocal(Body body, Type t) {
		Local local = Jimple.v().newLocal("$helper" + (counter++), t);
		body.getLocals().add(local);
		return local;
	}
	
}
