/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        DataflowResult<Node, Fact> prev_result = null;
        while (prev_result != result) {
            prev_result = result;
            int size = cfg.getNodes().size();
            Node[] list_nodes = (Node[])cfg.getNodes().toArray();
            for (int i = size - 1; i >= 0; i--) {
                Node n = list_nodes[i];
                if (n == cfg.getExit()) {
                    continue;
                }
                Set<Node> n_successes = cfg.getSuccsOf(n);
                for (Node n_success : n_successes) {
                    if (result.getOutFact(n) == null) {
                        result.setOutFact(n, result.getInFact(n_success));
                    } else {
                        this.analysis.meetInto(result.getInFact(n_success), result.getOutFact(n));
                    }
                }
                this.analysis.transferNode(n, result.getInFact(n), result.getOutFact(n));
            }
        }
    }
}
