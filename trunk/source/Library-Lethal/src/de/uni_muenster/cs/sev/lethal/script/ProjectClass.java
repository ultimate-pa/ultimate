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
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

/**
 * Class for representing the current workbench project in the script
 * Use Project.objectname to get the project objects
 * @author Philipp
 *
 */
public class ProjectClass extends ScriptClass { 
	
	/**
	 * Creates a new instance of the project class. To be used on script start.
	 * @param scriptObjects script objects to bind in the Project class environment
	 */
	public ProjectClass(final HashMap<String,ScriptObject> scriptObjects) {
		super("Project", null, RootClass.newStaticClassEnvironment(), false);
		
		final HashMap<ScriptObject, ArrayList<ScriptObject>> objectsByClass = new HashMap<ScriptObject, ArrayList<ScriptObject>>();
		
		for (String name : scriptObjects.keySet()){
			ScriptObject sobj = scriptObjects.get(name);
			this.setMember(name, sobj);
			
			ArrayList<ScriptObject> clist = objectsByClass.get(sobj.getParentClass());
			if (clist == null){
				clist = new ArrayList<ScriptObject>();
				objectsByClass.put(sobj.getParentClass(), clist);
			}
			clist.add(sobj);
		}
		
		this.setMember("all", new Method(Method.ARITY_ARBITARY){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				Collection<ScriptObject> classes;
				
				if (args.size() != 0){
					classes = args;
				} else {
					classes = objectsByClass.keySet();
				}
				
				List<ScriptObject> result;
				result = new ArrayList<ScriptObject>();
				for (ScriptObject sclass : classes){
					List<ScriptObject> clist = objectsByClass.get(sclass);
					if (clist != null){
						result.addAll(clist);
					}
				}
				return new ArrayObject(result);
			}
		});
		
		this.setMember("each", new Method(Method.ARITY_ARBITARY){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				if (block == null) throw new ScriptRuntimeError("Project.each() needs a block");
				int count = 0;
				Collection<ScriptObject> classes;
				
				if (args.size() != 0){
					classes = args;
				} else {
					classes = objectsByClass.keySet();
				}
				
				List<ScriptObject> argList = new ArrayList<ScriptObject>(1);
				argList.add(null); //dummy to make set work.)
				for (ScriptObject sclass : classes){
					List<ScriptObject> clist =  objectsByClass.get(sclass);
					if (clist != null){
						for (ScriptObject obj : clist){
							argList.set(0, obj);
							block.call(argList, null);
							count++;
						}
					}
				}
				return ScriptObject.make(count);
			}
		});
	}
	
	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		return null;
	}

}
