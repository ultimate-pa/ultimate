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

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

/**
 * Integer script number class
 * @author Philipp
 *
 */
public class IntegerClass extends ScriptClass {

	/** Singleton IntegerClass class instance */
	public static final IntegerClass integerClass = new IntegerClass();
	
	private IntegerClass() {
		super("Integer", null, RootClass.newStaticClassEnvironment(), false);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		return null;
	}

}

/**
 * Integer number object.
 * @author Philipp
 *
 */
class IntegerObject extends ScriptObject{
	
	private static final Environment integerInstEnv = IntegerClass.integerClass.newInstanceEnvironment(); //one shared instance env for all integer objects. Don't need one for each of them.
	{
		integerInstEnv.bindLocal("times", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (block == null) throw new ScriptRuntimeError("times() expects a block");
				List<ScriptObject> blockArgs = new ArrayList<ScriptObject>(1); 
				blockArgs.add(null);
				for (int i = 0; i < ((IntegerObject)env.getThis()).getValue(); i++){
					blockArgs.set(0, ScriptObject.make(i));
					block.call(blockArgs, null);
				}
				return ScriptObject.nullValue;
			}
		});
		integerInstEnv.bindLocal("even", integerInstEnv.bindLocal("even?", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make((((IntegerObject)env.getThis()).getValue() & 1) == 0 );
			}
		}));
		integerInstEnv.bindLocal("odd", integerInstEnv.bindLocal("odd?", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make(  ( ((IntegerObject)env.getThis()).getValue() & 1) != 0 );
			}
		}));

		integerInstEnv.bindLocal("<", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() < ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() < ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("< on Integer left value expects Integer or Float on right side");
				}
			}
		});
		integerInstEnv.bindLocal("<=", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() <= ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() <= ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("<= on Integer left value expects Integer or Float on right side");
				}
			}
		});
		
		integerInstEnv.bindLocal("+", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() + ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() + ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("+ on Integer expects Integer or Float on the other side");
				}
			}
		});
		integerInstEnv.bindLocal("-", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() - ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() - ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("- on Integer expects Integer or Float on the other side");
				}
			}
		});
		integerInstEnv.bindLocal("*", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() * ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() * ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("* on Integer expects Integer or Float on the other side");
				}
			}
		});
		integerInstEnv.bindLocal("/", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() / ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() / ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("/ on Integer expects Integer or Float on the other side");
				}
			}
		});
		integerInstEnv.bindLocal("%", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((IntegerObject)env.getThis()).getValue() % ((IntegerObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("% on Integer expects Integer the other side");
				}
			}
		});
		integerInstEnv.bindLocal("**", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( (int)Math.pow(((IntegerObject)env.getThis()).getValue() , ((IntegerObject)rightVal).getValue()) );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( Math.pow(((IntegerObject)env.getThis()).getValue() , ((FloatObject)rightVal).getValue()) );
				} else {
					throw new ScriptRuntimeError("** on Integer expects Integer or Float on the other side");
				}
			}
		});
		
		
		integerInstEnv.bindLocal("to_i", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return env.getThis();
			}
		});
		integerInstEnv.bindLocal("to_f", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make((double)((IntegerObject)env.getThis()).getValue());
			}
		});
		integerInstEnv.setOwner(IntegerClass.integerClass); //it is actually  an instance env, but it is shared among all instances. So we set the class as the owner.
	}
	
	private int value;
	
	public IntegerObject(int value) {
		super(IntegerClass.integerClass, integerInstEnv.newFrame());
		this.value = value;
	}
	
	public int getValue(){
		return this.value;
	}
	
	@Override
	public boolean equals(Object obj){
		return ((obj instanceof IntegerObject && ((IntegerObject)obj).getValue() == this.value)
			  ||(obj instanceof FloatObject && ((FloatObject)obj).getValue() == this.value));
	}
	
	@Override
	public String toString(){
		return String.valueOf(this.value);
	}

	@Override
	public int hashCode(){
		return this.value; //Integer hashCode() is the value itself
	}
}
