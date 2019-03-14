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

package pathexpression;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Table;
import pathexpression.RegEx.EmptySet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

public class PathExpressionComputer<N, V> {

  final static Logger logger = LogManager.getLogger(PathExpressionComputer.class);

  private LabeledGraph<N, V> graph;
  private BiMap<N, Integer> nodeToIntMap = HashBiMap.create();
  private Table<Integer, Integer, IRegEx<V>> table = HashBasedTable.create();
  private IRegEx<V> emptyRegEx = new RegEx.EmptySet<V>();
  private Map<N,List<IRegEx<V>>> allPathFromNode = new HashMap<>();
  private boolean eliminated;

  public PathExpressionComputer(LabeledGraph<N, V> graph) {
    this.graph = graph;
    initNodesToIntMap();
  }


  private void initNodesToIntMap() {
    int size = nodeToIntMap.size();
    for (N node : graph.getNodes()) {
      nodeToIntMap.put(node, (++size));
    }
  }

  private Integer getIntegerFor(N node) {
    assert nodeToIntMap.get(node) != null;
    return nodeToIntMap.get(node);
  }

  public IRegEx<V> getExpressionBetween(N a, N b) {
    if (!graph.getNodes().contains(a)) {
      return emptyRegEx;
    }
    List<IRegEx<V>> allExpr = computeAllPathFrom(a);
    return allExpr.get(getIntegerFor(b) - 1);
  }

  private List<IRegEx<V>> computeAllPathFrom(N a) {
    assert graph.getNodes().contains(a);
    if(allPathFromNode.get(a) != null) {
    		return allPathFromNode.get(a);
    }
    
    eliminate();
    logger.debug("Compute all path from {}", a);
    List<PathExpression<V>> extractPathSequence = extractPathSequence();
    List<IRegEx<V>> regEx = new ArrayList<>();
    for (int i = 0; i < graph.getNodes().size(); i++) {
      regEx.add(emptyRegEx);
    }
    regEx.set(getIntegerFor(a) - 1, new Epsilon<V>());
    for (int i = 0; i < extractPathSequence.size(); i++) {
      PathExpression<V> tri = extractPathSequence.get(i);
      if (tri.getSource() == tri.getTarget()) {
        IRegEx<V> expression = tri.getExpression();

        int vi = tri.getSource();
        IRegEx<V> regExVi = regEx.get(vi - 1);
        regEx.set(vi - 1, RegEx.<V>concatenate(regExVi, expression));

      } else {
        IRegEx<V> expression = tri.getExpression();
        int vi = tri.getSource();
        int wi = tri.getTarget();
        IRegEx<V> inter;
        IRegEx<V> regExVi = regEx.get(vi - 1);
        inter = RegEx.<V>concatenate(regExVi, expression);

        IRegEx<V> regExWi = regEx.get(wi - 1);
        regEx.set(wi - 1, RegEx.<V>union(regExWi, inter));
      }
    }
    allPathFromNode.put(a, regEx);
    logger.debug("End extraction all path");
    return regEx;
  }

  private List<PathExpression<V>> extractPathSequence() {
    int n = graph.getNodes().size();
    List<PathExpression<V>> list = new ArrayList<PathExpression<V>>();
    for (int u = 1; u <= n; u++) {
      for (int w = u; w <= n; w++) {
        IRegEx<V> reg = table.get(u, w);
        if (!(reg instanceof EmptySet) && !(reg instanceof Epsilon)) {
          list.add(new PathExpression<V>(reg, u, w));
        }
      }
    }
    for (int u = n; u > 0; u--) {
      for (int w = 1; w < u; w++) {
        IRegEx<V> reg = table.get(u, w);
        if (!(reg instanceof EmptySet)) {
          list.add(new PathExpression<V>(reg, u, w));
        }
      }
    }
    return list;
  }

  private void eliminate() {
	if(eliminated) {
	  return;
	}
	logger.debug("Start eliminating");
    int numberOfNodes = graph.getNodes().size();
    for (int v = 1; v <= numberOfNodes; v++) {
      for (int w = 1; w <= numberOfNodes; w++) {
        if (v == w) {
          updateTable(v, w, new Epsilon());
        } else {
          updateTable(v, w, emptyRegEx);
        }
      }
    }
    for (Edge<N, V> e : graph.getEdges()) {
      Integer head = getIntegerFor(e.getStart());
      Integer tail = getIntegerFor(e.getTarget());
      IRegEx<V> pht = table.get(head, tail);
      pht = RegEx.<V>union(new RegEx.Plain<V>(e.getLabel()), pht);
      updateTable(head, tail, pht);
    }
    for (int v = 1; v <= numberOfNodes; v++) {
      IRegEx<V> pvv = table.get(v, v);
      pvv = RegEx.<V>star(pvv);
      updateTable(v, v, pvv);
      for (int u = v + 1; u <= numberOfNodes; u++) {
        IRegEx<V> puv = table.get(u, v);
        if (puv instanceof EmptySet) {
          continue;
        }
        puv = RegEx.<V>concatenate(puv, pvv);
        updateTable(u, v, puv);
        for (int w = v + 1; w <= numberOfNodes; w++) {
          IRegEx<V> pvw = table.get(v, w);
          if (pvw instanceof EmptySet) {
            continue;
          }

          IRegEx<V> old_puw = table.get(u, w);
          IRegEx<V> a = RegEx.<V>concatenate(puv, pvw);
          IRegEx<V> puw = RegEx.<V>union(old_puw, a);
          updateTable(u, w, puw);
        }
      }
    }
    eliminated = true;
    logger.debug("End eliminating");
  }


  private void updateTable(Integer i, Integer j, IRegEx<V> reg) {
    table.put(i, j, reg);
  }

}
