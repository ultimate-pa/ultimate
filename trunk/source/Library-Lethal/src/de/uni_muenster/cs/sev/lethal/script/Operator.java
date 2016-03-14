/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.script;

import java.util.ArrayList;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptParseException;
import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

/**
 * Base class for Operators with static methods to create them
 * @author Philipp
 *
 */
public abstract class Operator extends Expression {
	protected Expression right;
	
	protected boolean bound;
	
	/**
	 * Returns a binary operator of the for a given name
	 * The operator is in unbound state, meaning that no operands have been given to it yet.
	 * This has to be done by using the bind() method before using it.
	 * @param script currently parsed script 
	 * @param name name of the operator
	 * @return operator of the for a given name
	 */
	public static BinaryOperator makeBinaryOperator(StringReader script, String name){
		if (name.equals("=")) return new Assign();
		else if (name.equals("+"))  return new AddConcat();
		else if (name.equals("-"))  return new MethodOperator("-", false, 3);
		else if (name.equals("*"))  return new MethodOperator("*", false, 5);
		else if (name.equals("/"))  return new MethodOperator("/", false, 5);
		else if (name.equals("%"))  return new MethodOperator("%", false, 6);
		else if (name.equals("**")) return new MethodOperator("**", false, 7);
		else if (name.equals("<"))  return new MethodOperator("<",false,2);
		else if (name.equals(">"))  return new MethodOperator("<", true,2);
		else if (name.equals("<=") || name.equals("=<")) return new MethodOperator("<=", false, 2);
		else if (name.equals(">=") || name.equals("=>")) return new MethodOperator("<=", true, 2);
		else if (name.equals("!=")) return new NotEqual();
		else if (name.equals("==")) return new MethodOperator("==", false,2);
		else if (name.equals("&&")) return new And();
		else if (name.equals("||")) return new Or();
		else if (name.equals("^"))  return new Xor();
		else if (name.equals("..")) return new RangeOp();
		else throw new ScriptParseException(script.getCurrentLine(), "Binary Operator '" + name + "' not found");
	}

	/**
	 * Returns an unary operator of the for a given name
	 * The operator is in unbound state, meaning that no operands have been given to it yet.
	 * This has to be done by using the bind() method before using it.
	 * @param script currently parsed script 
	 * @param name name of the operator
	 * @return operator of the for a given name
	 */
	public static UnaryOperator makeUnaryOperator(StringReader script, String name){
		if (name.equals("-")){
			return new Sign();
		} else if (name.equals("!")){
			return new Not();
		} else throw new ScriptParseException(script.getCurrentLine(), "Unary Operator '" + name + "' not found");
	}
	
	/**
	 * Returns true if the operator has been bound to its operands, false if not.
	 * @return true if the operator has been bound to its operands, false if not.
	 */
	public boolean isBound(){
		return bound;
	}
	
	/**
	 * Get the bind weight of this operator
	 * A higher value means a stronger binding to its neighbor expressions.
	 * The operator with the highest bind weight will be evaluated first.
	 * @return the bind weight of this operator
	 */
	public abstract int getBindWeight();
}

/**
 * Base class for unary operators
 * @author Philipp
 *
 */
abstract class UnaryOperator extends Operator{
	/**
	 * bind the unary operator to its right expression
	 * @param right expression on the right side of the operator
	 */
	public void bind(Expression right){
		this.right = right;
		this.bound = true;
	}
}

/**
 * Flip sign operator
 * @author Philipp
 *
 */
class Sign extends UnaryOperator{
	@Override
	public ScriptObject execute(Environment env) {
		ScriptObject vright = right.execute(env);
		//Ugh...
		if (vright instanceof IntegerObject){
			return ScriptObject.make( - ((IntegerObject)vright).getValue()); 
		} else if (vright instanceof FloatObject){
			return ScriptObject.make( - ((FloatObject)vright).getValue());
		} else {
			throw new ScriptRuntimeError("Operator - expects numeric argument");
		}
	}
	@Override
	public int getBindWeight(){return 8;}
}

/**
 * Boolean not operator
 * @author Philipp
 *
 */
class Not extends UnaryOperator{
	@Override
	public ScriptObject execute(Environment env) {
		ScriptObject vright = right.execute(env);
		//Ugh...
		if (vright instanceof BooleanObject){
			return ScriptObject.make( !((BooleanObject)vright).getValue()); 
		} else {
			throw new ScriptRuntimeError("Operator ! expects boolean argument");
		}
	}
	@Override
	public int getBindWeight(){return 8;}
}

/**
 * Base class for binary operators
 * @author Philipp
 *
 */
abstract class BinaryOperator extends Operator{
	protected Expression left;
	
	/**
	 * Bind the binary operator to its left and right expressions 
	 * @param left left side expression
	 * @param right right side expression
	 */
	public void bind(Expression left, Expression right){
		this.left = left;
		this.right = right;
		this.bound = true;
	}
}

/**
 * Assignment operator (binds name left side to the right side value) 
 * @author Philipp
 *
 */
class Assign extends BinaryOperator{

	@Override
	public ScriptObject execute(Environment env) {
		if (!(this.left instanceof Evaluation)) throw new ScriptRuntimeError("Left side of assignment must be a variable");
		ScriptObject vright = right.execute(env);
		((Evaluation)this.left).write(env, vright);
		return vright;
	}

	@Override
	public int getBindWeight() {return 0;}
}

/**
 * Class for method calling operators
 * Evaluates its operands and then calls the method with the given name on its evaluated left (or right if swap is set) operand
 * and passes the evaluated right (or left is swap is set) operand
 * @author Philipp
 *
 */
class MethodOperator extends BinaryOperator{
	
	private String method;
	private boolean swap;
	private int bindWeight;
	
	public MethodOperator(String method, boolean swap, int bindWeight){
		this.method = method;
		this.swap = swap;
		this.bindWeight = bindWeight;
	}
	
	
	@Override
	public void bind(Expression left, Expression right) {
		if (swap){
			super.bind(right, left);
		} else {
			super.bind(left, right);
		}
	}

	@Override
	public ScriptObject execute(Environment env) {
		ScriptObject vleft = left.execute(env);
		ScriptObject vright = right.execute(env);
		Method m = vleft.getMethod(this.method);
		List<ScriptObject> args = new ArrayList<ScriptObject>(1);
		args.add(vright);
		return m.execute(vleft.getEnvironment(), args , null);
	}
	@Override
	public int getBindWeight(){return this.bindWeight;}
}


/**
 * Special + operator to handle ConCat of strings on both sides without the need to make every class implement the + method for strings.
 * If none of the operands is a string it behaves like the method operator for +
 * @author Philipp
 *
 */
class AddConcat extends BinaryOperator{

	@Override
	public ScriptObject execute(Environment env) {
		ScriptObject vleft = left.execute(env);
		ScriptObject vright = right.execute(env);
		if (vleft instanceof StringObject || vright instanceof StringObject){
			return new StringObject(vleft.toString() + vright.toString());
		} else {
			Method m = vleft.getMethod("+");
			List<ScriptObject> args = new ArrayList<ScriptObject>(1);
			args.add(vright);
			return m.execute(vleft.getEnvironment(), args , null);
		}
	}
	@Override
	public int getBindWeight(){return 3;}
}

/**
 * Special != operator, calls == on the left object and inverts the result.
 * @author Philipp
 *
 */
class NotEqual extends BinaryOperator{

	@Override
	public ScriptObject execute(Environment env) {
		ScriptObject vleft = left.execute(env);
		ScriptObject vright = right.execute(env);
		Method m = vleft.getMethod("==");
		List<ScriptObject> args = new ArrayList<ScriptObject>(1);
		args.add(vright);
		return ScriptObject.make((!m.execute(vleft.getEnvironment(), args , null).isTrue()));
	}
	@Override
	public int getBindWeight(){return 2;}
}

/**
 * Boolean and operator
 * @author Philipp
 *
 */
class And extends BinaryOperator{
	@Override
	public ScriptObject execute(Environment env) {
		ScriptObject vleft = left.execute(env);
		ScriptObject vright = right.execute(env);
		return ScriptObject.make(vleft.isTrue() && vright.isTrue());
	}
	@Override
	public int getBindWeight() {return 1;}
}
/**
 * Boolean inclusive or operator
 * @author Philipp
 *
 */
class Or extends BinaryOperator{
	@Override
	public ScriptObject execute(Environment env) {
		ScriptObject vleft = left.execute(env);
		ScriptObject vright = right.execute(env);
		return ScriptObject.make(vleft.isTrue() || vright.isTrue());
	}
	@Override
	public int getBindWeight() {return 1;}
}
/**
 * Boolean exclusive or operator
 * @author Philipp
 *
 */
class Xor extends BinaryOperator{
	@Override
	public ScriptObject execute(Environment env) {
		ScriptObject vleft = left.execute(env);
		ScriptObject vright = right.execute(env);
		return ScriptObject.make(vleft.isTrue() ^ vright.isTrue());
	}
	@Override
	public int getBindWeight() {return 1;}
}

/**
 * a..b Operator to create ranges of Integers. Shortcut for Range.new(a,b)
 * @author Philipp
 *
 */
class RangeOp extends BinaryOperator{
	@Override
	public ScriptObject execute(Environment env) {
		ArrayList<ScriptObject> args = new ArrayList<ScriptObject>(2);
		args.add(left.execute(env));
		args.add(right.execute(env));
		return ((RangeClass)env.get("Range")).newInstance(args, null);
	}
	@Override
	public int getBindWeight() {return 0;}
}
