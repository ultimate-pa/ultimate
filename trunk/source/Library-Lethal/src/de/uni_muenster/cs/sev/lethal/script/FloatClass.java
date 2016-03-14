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

import java.util.List;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

/**
 * ScriptClass representing float values (with double precision).
 * @author Philipp
 *
 */
public class FloatClass extends ScriptClass {

	/** Singleton FloatClass class instance */
	public static final FloatClass floatClass = new FloatClass();
	
	private FloatClass() {
		super("Float", null, RootClass.newStaticClassEnvironment(), false);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		return null;
	}

}

/**
 * ScriptObject representing a float value
 * @author Philipp
 *
 */
class FloatObject extends ScriptObject{
	
	private static final Environment floatInstEnv = FloatClass.floatClass.newInstanceEnvironment(); //one shared instance env for all float objects. Don't need one for each of them.
	{
		floatInstEnv.bindLocal("<", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() < ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() < ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("< on Float left value expects Integer or Float on right side");
				}
			}
		});
		floatInstEnv.bindLocal("<=", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() <= ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() <= ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("<= on Float left value expects Integer or Float on right side");
				}
			}
		});

		floatInstEnv.bindLocal("+", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() + ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() + ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("+ on Float expects Integer or Float on the other side");
				}
			}
		});
		floatInstEnv.bindLocal("-", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() - ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() - ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("- on Float expects Integer or Float on the other side");
				}
			}
		});
		floatInstEnv.bindLocal("*", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() * ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() * ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("* on Float expects Integer or Float on the other side");
				}
			}
		});
		floatInstEnv.bindLocal("/", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() / ((IntegerObject)rightVal).getValue() );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( ((FloatObject)env.getThis()).getValue() / ((FloatObject)rightVal).getValue() );
				} else {
					throw new ScriptRuntimeError("/ on Float expects Integer or Float on the other side");
				}
			}
		});
		floatInstEnv.bindLocal("**", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof IntegerObject){
					return ScriptObject.make( Math.pow(((FloatObject)env.getThis()).getValue() , ((IntegerObject)rightVal).getValue()) );
				} else if (rightVal instanceof FloatObject){
					return ScriptObject.make( Math.pow(((FloatObject)env.getThis()).getValue() , ((FloatObject)rightVal).getValue()) );
				} else {
					throw new ScriptRuntimeError("** on Float expects Integer or Float on the other side");
				}
			}
		});
		
		
		floatInstEnv.bindLocal("to_i", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make( (int)((FloatObject)env.getThis()).getValue() );
			}
		});
		floatInstEnv.bindLocal("to_f", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return env.getThis();
			}
		});
		floatInstEnv.setOwner(FloatClass.floatClass); //it is actually  an instance env, but it is shared among all instances. So we set the class as the owner.
	}
	
	private double value;
	
	/**
	 * Create a new FloatObject
	 * @param value value to represent
	 */
	public FloatObject(double value) {
		super(FloatClass.floatClass, floatInstEnv.newFrame());
		this.value = value;
	}
	
	/**
	 * Returns the value represented by this FloatObject
	 * @return the value represented by this FloatObject
	 */
	public double getValue(){
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
		return ((Double)this.value).hashCode();
	}
}
