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
 * Class for User defined script classes.
 * @author Philipp
 *
 */
class UserClass extends ScriptClass{
	
	public UserClass(String className, ScriptClass parentClass, Environment classEnvironment) {
		super(className, parentClass, classEnvironment, true);
	}
	
	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block){
		UserObject instance = new UserObject(this);
		Method constructor;
		try{
			constructor = instance.getMethod("initialize");
			if (!constructor.checkArity(args.size())) throw new ScriptRuntimeError("Construtor for class " + getClassName() + " expects " + constructor.getArityString() + " args, got " + args.size());
		} catch (UndefinedMemberException ex){
			return instance; //no constructor, we are done. 
		}
		
		constructor.execute(instance.getEnvironment().newFrame(), args, null);
		
		return instance;
	}
	
	@Override
	public int hashCode(){
		return this.getParentClass().hashCode() + (31 * this.getEnvironment().hashCode());
	}
}

/**
 * Object for user defined script classes
 * @author Philipp
 *
 */
class UserObject extends ScriptObject{

	private static final Method userObjDefaultEquals = new Method(1){
		@Override
		public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
			return ScriptObject.make(args.get(0) == env.getThis());
		}
	};
	
	public UserObject(ScriptClass parentClass) {
		super(parentClass);
		this.setMember("==", userObjDefaultEquals);
	}
	
	@Override
	public String toString(){
		try {
			return ((StringObject)(this.getMethod("to_s")).execute(getEnvironment(), new ArrayList<ScriptObject>(), null)).getValue();
		} catch (UndefinedMemberException ex){
			return this.getClassName();
		}
	}
	
	@Override
	public boolean equals(Object o){
		if (!(o instanceof ScriptObject)) return false;
		
		ArrayList<ScriptObject> argList = new ArrayList<ScriptObject>(1);
		argList.add((ScriptObject)o);
		try {
			return (this.getMethod("==")).execute(getEnvironment(), argList, null) == ScriptObject.trueValue;
		} catch (UndefinedMemberException ex){
			return o == this;
		}
		
	}
	
	@Override
	public int hashCode(){
		return this.getParentClass().hashCode() + (31 * this.getEnvironment().hashCode());
	}
}
