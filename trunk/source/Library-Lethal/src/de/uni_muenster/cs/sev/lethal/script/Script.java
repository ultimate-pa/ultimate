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

import de.uni_muenster.cs.sev.lethal.gui.*;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

/**
 * Script object, representing a parsed script, ready to be run.
 * @author Philipp
 *
 */
public class Script {
	
	private List<Statement> statements;
	
	protected Script(List<Statement> statements) {
		this.statements = statements;
	}
	
	/**
	 * Run the script without project workspace and with output directed to STDOUT
	 */
	public void execute() {
		execute(System.out, null);
	}
	
	/**
	 * Run the script with output written to the given stream, but without a project attached.
	 * @param out output stream
	 */
	public void execute(PrintStream out) {
		execute(out, null);
	}
	
	/**
	 * Run the script with given project workspace and output written to the given stream
	 * @param out stream to write the output to
	 * @param project project providing predefined additional objects. if project is null no "Project" object will be bound in the script namespace
	 */
	public void execute(PrintStream out, Project project) {
		RootObject rootObject = new RootObject(out, project);
		Environment rootEnv = rootObject.getEnvironment();
		
		
		if (project != null) {
			HashMap<String,ScriptObject> scriptObjects = new HashMap<String,ScriptObject>();
			
			for (Item item : project.getItems(FTAItem.class)){
				scriptObjects.put(item.getName(), new FTAObject(((FTAItem)item).getAutomaton()));
			}
			for (Item item : project.getItems(TreeItem.class)){
				if (((TreeItem)item).getTree() != null) scriptObjects.put(item.getName(), new TreeObject(((TreeItem)item).getTree()));
			}
			for (Item item : project.getItems(HomomorphismItem.class)){
				scriptObjects.put(item.getName(), new HomomorphismObject(((HomomorphismItem)item).getHomomorphism()));
			}
			for (Item item : project.getItems(TreeTransducerItem.class)){
				scriptObjects.put(item.getName(), new TreeTransducerObject(((TreeTransducerItem)item).getTreeTransducer()));
			}
			for (Item item : project.getItems(HedgeItem.class)){
				scriptObjects.put(item.getName(), new HedgeObject(((HedgeItem)item).getTree()));
			}
			for (Item item : project.getItems(HedgeAutomatonItem.class)){
				scriptObjects.put(item.getName(), new HAObject(((HedgeAutomatonItem)item).getAutomaton()));
			}

			ProjectClass projectClass = new ProjectClass(scriptObjects);
			rootObject.getEnvironment().bindLocal("Project", projectClass);
		}
		
		try{
			for (Statement statement : this.statements){
				statement.execute(rootEnv);
			}
		} catch (Break.BreakException ex) {
			throw new ScriptRuntimeError("Break outside loop");
		} catch (Return.ReturnException ex) {
			throw new ScriptRuntimeError("Return outside method");
		}
	}

}
