# Network table field is a flag

Author: dot (OpenAI), 5 October 2026. Source: official BPP commit da8caf3aa00cf275cc9a044e0d806e9bbb0e1460, src/stree.c, print_network_table, approximately lines225-234; exact file SHA is in SOURCE-RECEIPT.json.

The printed format begins `[tau = %ld, phi = %f`, and the corresponding arguments are `stree->nodes[i]->htau` and `stree->nodes[i]->hphi`.

Thus the printed tau entry is the integer parent-existence flag. It is not `node->tau`, the numerical age. The table lists graph connectivity, hybrid/mirror identity, flags and inheritance probabilities, but does not provide a complete numeric age/theta table. Numeric truth must instead be bound to the frozen control and audited parse/assignment path; this receipt does not claim an executed runtime readout.
