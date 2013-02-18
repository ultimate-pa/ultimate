/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model
 * File:	GraphNotFoundException.java created on Nov 11, 2009 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.model;


/**
 * GraphNotFoundException
 *
 * @author Björn Buchhold
 *
 */
public class GraphNotFoundException extends Exception {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -6102010750779099260L;


	/**
	 * @param gt the graph that could not be found
	 * @param e the exception thrown
	 */
	public GraphNotFoundException(GraphType gt, Exception e) {
		super("The Graphtype: " + gt + " could not be found. Neither in the map, nor in the repository" , e);
	}


	/**
	 * @param gt
	 */
	public GraphNotFoundException(GraphType gt) {
		super("The Graphtype: " + gt + " could not be found. Neither in the map, nor in the repository");
	}

}
