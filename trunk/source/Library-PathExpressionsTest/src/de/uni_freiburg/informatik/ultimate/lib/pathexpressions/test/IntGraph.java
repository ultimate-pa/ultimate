/*******************************************************************************
 * Copyright (c) 2018 Fraunhofer IEM, Paderborn, Germany.
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * http://www.eclipse.org/legal/epl-2.0.
 *  
 * SPDX-License-Identifier: EPL-2.0
 *
 * Contributors:
 *     Johannes Spaeth - initial API and implementation
 *******************************************************************************/
package test;
import java.util.Set;

import com.google.common.collect.Sets;

import pathexpression.Edge;
import pathexpression.LabeledGraph;


public class IntGraph implements LabeledGraph<Integer, String> {

  private Set<Edge<Integer, String>> edges = Sets.newHashSet();
  private Set<Integer> nodes = Sets.newHashSet();

  public void addEdge(int start, String label, int target) {
    nodes.add(start);
    nodes.add(target);
    edges.add(new IntEdge(start, label, target));
  }

  @Override
  public Set<Edge<Integer, String>> getEdges() {
    return edges;
  }

  @Override
  public Set<Integer> getNodes() {
    return nodes;
  }

}
