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
 * Script Class for character strings.
 * @author Philipp
 *
 */
public class StringClass extends ScriptClass {

	/** Singleton StringClass class instance */
	public static final StringClass stringClass = new StringClass();
	
	private StringClass() {
		super("String", null, RootClass.newStaticClassEnvironment(), false);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		return null;
	}

}
/**
 * Script Object for character strings.
 * @author Philipp
 *
 */
class StringObject extends ScriptObject{
	
	private static final Environment stringInstEnv = StringClass.stringClass.newInstanceEnvironment(); //one shared instance env for all integer objects. Don't need one for each of them.
	{
		stringInstEnv.bindLocal("+", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make(env.toString() + args.get(0).toString());
			}
		});
		stringInstEnv.bindLocal("<", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof StringObject){
					return ScriptObject.make( ((StringObject)env.getThis()).getValue().compareTo(((StringObject)rightVal).getValue()) < 0 );
				} else {
					throw new ScriptRuntimeError("< on String left value expects String on right side");
				}
			}
		});
		stringInstEnv.bindLocal("<=", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				ScriptObject rightVal = args.get(0);
				if (rightVal instanceof StringObject){
					return ScriptObject.make( ((StringObject)env.getThis()).getValue().compareTo(((StringObject)rightVal).getValue()) <= 0 );
				} else {
					throw new ScriptRuntimeError("<= on String left value expects String on right side");
				}
			}
		});
		
		stringInstEnv.bindLocal("length", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make(((StringObject)env.getThis()).getValue().length());
			}
		});
		stringInstEnv.bindLocal("substring", new Method(Method.ARITY_ONE_OR_TWO){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (!(args.get(0) instanceof IntegerObject)) throw new ScriptRuntimeError("String.substring expects integer arguments");
				int beginIndex = ((IntegerObject)args.get(0)).getValue();
				if (args.size() == 1){
					return ScriptObject.make( ((StringObject)env.getThis()).getValue().substring(beginIndex));
				} else {
					if (!(args.get(1) instanceof IntegerObject)) throw new ScriptRuntimeError("String.substring expects integer arguments");
					int endIndex = ((IntegerObject)args.get(1)).getValue();
					return ScriptObject.make( ((StringObject)env.getThis()).getValue().substring(beginIndex,endIndex));
				}
			}
		});

		stringInstEnv.bindLocal("to_i", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make( Integer.valueOf(((StringObject)env.getThis()).getValue()) );
			}
		});
		
		stringInstEnv.setOwner(StringClass.stringClass);
	}
	
	private String value;
	
	public StringObject(String value) {
		super(StringClass.stringClass, stringInstEnv.newFrame());
		this.value = value;
	}
	
	public String getValue(){
		return this.value;
	}
	
	@Override
	public boolean equals(Object obj){
		return (obj instanceof StringObject && ((StringObject)obj).getValue().equals(this.value));
	}
	
	@Override
	public String toString(){
		return String.valueOf(this.value);
	}
	
	@Override
	public int hashCode(){
		return this.value.hashCode();
	}
}
