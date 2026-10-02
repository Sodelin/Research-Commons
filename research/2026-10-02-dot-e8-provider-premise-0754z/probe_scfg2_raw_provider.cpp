#include "scfg2/deductions/generate_exact_basic.hh"
#include "scfg2/engine/basic_schedule.hh"
#include "sparse_tree.hh"
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <algorithm>

namespace d = cparty::scfg2::deductions;
namespace g = cparty::scfg2::grammar;
struct Context final : d::PairabilityContext {
  mutable sparse_tree tree;
  std::string sequence;
  explicit Context(std::string s) : tree(s, static_cast<int>(s.size())) {}
  cand_pos_t turn() const override { return 3; }
  cand_pos_t sequence_length() const override { return tree.n; }
  bool can_pair(cand_pos_t i, cand_pos_t j) const override {
    if (!(1 <= i && i < j && j <= tree.n)) return false;
    if (sequence.empty()) return true;
    const std::string pair{sequence[i-1],sequence[j-1]};
    return pair=="AU"||pair=="UA"||pair=="CG"||pair=="GC"||pair=="GU"||pair=="UG";
  }
  cand_pos_t unpaired_prefix(cand_pos_t i) const override {
    return 0 <= i && i <= tree.n ? tree.up[i] : 0;
  }
  cand_pos_t pair_partner(cand_pos_t i) const override {
    return 1 <= i && i <= tree.n ? tree.tree[i].pair : -1;
  }
  cand_pos_t parent_index(cand_pos_t i) const override {
    return 1 <= i && i <= tree.n ? tree.tree[i].parent->index : -1;
  }
  cand_pos_t border_b(cand_pos_t i, cand_pos_t j) const override { return tree.b(i,j); }
  cand_pos_t border_bp(cand_pos_t i, cand_pos_t j) const override { return tree.bp(i,j); }
  cand_pos_t border_B(cand_pos_t i, cand_pos_t j) const override { return tree.B(i,j); }
  cand_pos_t border_Bp(cand_pos_t i, cand_pos_t j) const override { return tree.Bp(i,j); }
  bool is_unpaired(cand_pos_t i) const override {
    return 1 <= i && i <= tree.n && tree.tree[i].pair < 0;
  }
  bool weakly_closed(cand_pos_t i, cand_pos_t j) const override { return tree.weakly_closed(i,j); }
};
bool same(const d::ItemKey&a,const d::ItemKey&b) { return d::ItemKeyEq{}(a,b); }
void key(const d::ItemKey& x) {
  std::cout << "[" << static_cast<int>(x.nonterminal) << "," << x.i << "," << x.j
    << "," << x.ip << "," << x.jp << "]";
}
int main(int argc, char** argv) {
  const int requested_split = argc>1 ? std::stoi(argv[1]) : 9;
  std::string s(21,'.');
  s[0]='(';s[19]=')';s[7]='(';s[14]=')';
  Context ctx(s);
  ctx.sequence=std::string(21,'A');
  for(int pos : {1,7,8,13})ctx.sequence[pos-1]='G';
  for(int pos : {12,15,20,21})ctx.sequence[pos-1]='C';
  d::ItemKey parent{g::NonTerminal::WMBP,7,21,-1,-1};
  auto schedule=cparty::scfg2::engine::build_pkfree_basic_exact_schedule(21,ctx);
  auto position=[&](const d::ItemKey& item) {
    for(size_t z=0;z<schedule.size();++z) if(same(schedule[z],item)) return z;
    return schedule.size();
  };
  auto provider=d::generate_exact_basic_deductions_for_item(parent,ctx);
  using Nat=uint64_t;
  constexpr Nat maximum=std::numeric_limits<Nat>::max();
  auto checked_add=[&](Nat a,Nat b) {if(b>maximum-a)throw std::overflow_error("addition");return a+b;};
  std::unordered_map<d::ItemKey,Nat,d::ItemKeyHash,d::ItemKeyEq> chart;
  auto normalized=[](const d::Deduction& ded,size_t z) {
    auto child=ded.children[z].item;
    if(ded.rule==g::RuleId::WMBP_DIRECT_VP && child.nonterminal==g::NonTerminal::VP_DIRECT)
      child=d::ItemKey{g::NonTerminal::VP,child.i,child.j,-1,-1};
    return child;
  };
  auto contribution=[&](const d::Deduction& ded) {
    Nat term=1;
    for(size_t z=0;z<ded.child_count;++z) {
      Nat child=chart[normalized(ded,z)];
      if(term && child>maximum/term)throw std::overflow_error("multiplication");
      term*=child;
    }
    return term;
  };
  for(const auto& item:schedule) {
    Nat total=0;
    for(const auto& ded:d::generate_exact_basic_deductions_for_item(item,ctx))total=checked_add(total,contribution(ded));
    chart[item]=total;
  }
  Nat recomputed=0;
  for(const auto& ded:provider)recomputed=checked_add(recomputed,contribution(ded));
  auto phase=[](g::NonTerminal nt) {
    switch(nt) {
      case g::NonTerminal::VM:return 0;case g::NonTerminal::V:return 1;
      case g::NonTerminal::WMv:return 2;case g::NonTerminal::VP_CLOSED:return 3;
      case g::NonTerminal::VP:return 4;case g::NonTerminal::VP_DIRECT:return 5;
      case g::NonTerminal::BE:return 6;case g::NonTerminal::VPL:return 7;
      case g::NonTerminal::VPR:return 8;case g::NonTerminal::WMBP:return 9;
      case g::NonTerminal::WMBW:return 10;case g::NonTerminal::WMB:return 11;
      case g::NonTerminal::WMp:return 12;case g::NonTerminal::WM:return 13;
      case g::NonTerminal::WIP:return 14;case g::NonTerminal::WI:return 15;
      case g::NonTerminal::W:return 16;
    }return 17;
  };
  auto proposed=schedule;
  std::stable_sort(proposed.begin(),proposed.end(),[&](const d::ItemKey&a,const d::ItemKey&b){
    if(a.j!=b.j)return a.j<b.j;
    if(a.nonterminal==g::NonTerminal::BE && b.nonterminal!=g::NonTerminal::BE)return true;
    if(b.nonterminal==g::NonTerminal::BE && a.nonterminal!=g::NonTerminal::BE)return false;
    if(a.nonterminal==g::NonTerminal::BE)return false;
    if(a.i!=b.i)return a.i>b.i;
    return phase(a.nonterminal)<phase(b.nonterminal);
  });
  auto bad_edges=[&](const std::vector<d::ItemKey>& order) {
    std::unordered_map<d::ItemKey,size_t,d::ItemKeyHash,d::ItemKeyEq> at;
    for(size_t z=0;z<order.size();++z)at[order[z]]=z;
    size_t bad=0,unknown=0,edges=0;
    for(size_t z=0;z<order.size();++z)
      for(const auto& ded:d::generate_exact_basic_deductions_for_item(order[z],ctx))
        for(size_t c=0;c<ded.child_count;++c) {
          ++edges;auto child=normalized(ded,c);auto it=at.find(child);
          if(it==at.end())++unknown;else if(it->second>=z)++bad;
        }
    return std::array<size_t,3>{bad,unknown,edges};
  };
  auto original_edges=bad_edges(schedule),proposed_edges=bad_edges(proposed);
  std::unordered_map<d::ItemKey,Nat,d::ItemKeyHash,d::ItemKeyEq> reordered;
  for(const auto& item:proposed) {
    Nat total=0;
    for(const auto& ded:d::generate_exact_basic_deductions_for_item(item,ctx)) {
      Nat term=1;
      for(size_t z=0;z<ded.child_count;++z) {
        Nat child=reordered[normalized(ded,z)];
        if(term && child>maximum/term)throw std::overflow_error("reordered multiplication");
        term*=child;
      }
      total=checked_add(total,term);
    }
    reordered[item]=total;
  }
  const d::ItemKey root{g::NonTerminal::W,1,21,-1,-1};
  auto root_cone=[&](bool productive_only) {
    std::unordered_set<d::ItemKey,d::ItemKeyHash,d::ItemKeyEq> seen;
    std::vector<d::ItemKey> todo{root};size_t future=0,edges=0;
    while(!todo.empty()) {
      auto item=todo.back();todo.pop_back();if(!seen.insert(item).second)continue;
      for(const auto& ded:d::generate_exact_basic_deductions_for_item(item,ctx)) {
        bool productive=true;
        for(size_t z=0;z<ded.child_count;++z)if(reordered[normalized(ded,z)]==0)productive=false;
        if(productive_only && !productive)continue;
        for(size_t z=0;z<ded.child_count;++z) {
          auto child=normalized(ded,z);++edges;
          if(position(child)>=position(item))++future;
          todo.push_back(child);
        }
      }
    }
    return std::array<size_t,3>{seen.size(),edges,future};
  };
  auto raw_cone=root_cone(false),productive_cone=root_cone(true);
  std::cout << "{\"scaffold\":\"" << s << "\",\"parent_position\":" << position(parent)
    << ",\"sequence\":\""<<ctx.sequence<<"\",\"weight_model\":\"unit local factors, overflow-checked natural counts\""
    << ",\"final_cached_parent\":\""<<chart[parent]<<"\",\"recomputed_from_final_chart\":\""<<recomputed<<"\""
    << ",\"baseline_future_edges\":"<<original_edges[0]<<",\"baseline_unknown_children\":"<<original_edges[1]
    << ",\"checked_dependency_edges\":"<<original_edges[2]<<",\"candidate_future_edges\":"<<proposed_edges[0]
    << ",\"candidate_unknown_children\":"<<proposed_edges[1]<<",\"candidate_parent_count\":\""<<reordered[parent]<<"\""
    << ",\"baseline_root_count\":\""<<chart[d::ItemKey{g::NonTerminal::W,1,21,-1,-1}]<<"\""
    << ",\"candidate_root_count\":\""<<reordered[d::ItemKey{g::NonTerminal::W,1,21,-1,-1}]<<"\""
    << ",\"root_raw_cone\":{\"items\":"<<raw_cone[0]<<",\"edges\":"<<raw_cone[1]<<",\"future\":"<<raw_cone[2]<<"}"
    << ",\"root_productive_unit_cone\":{\"items\":"<<productive_cone[0]<<",\"edges\":"<<productive_cone[1]<<",\"future\":"<<productive_cone[2]<<"}"
    << ",\"requested_split\":" << requested_split
    << ",\"border_values\":[" << ctx.border_b(7,21) << "," << ctx.border_bp(7,requested_split)
    << "," << ctx.border_B(requested_split,21) << "," << ctx.border_Bp(requested_split,21) << "],\"deductions\":[";
  bool first=true;int found=0;
  for (const auto& ded:provider) {
    if ((ded.rule!=g::RuleId::WMBP_SPLIT_BE_WMBP_VP && ded.rule!=g::RuleId::WMBP_SPLIT_BE_WMBW_VP)
        ||ded.split.k!=requested_split) continue;
    if(!first) std::cout<<",";first=false;++found;
    std::cout<<"{\"valid\":" << (d::is_valid(ded)?"true":"false") << ",\"rule\":"
      << static_cast<int>(ded.rule)<<",\"children\":[";
    for(int z=0;z<ded.child_count;++z) {
      if(z)std::cout<<",";
      std::cout<<"{\"key\":";key(ded.children[z].item);
      std::cout<<",\"schedule_position\":"<<position(ded.children[z].item)
        <<",\"provider_count\":"<<d::generate_exact_basic_deductions_for_item(ded.children[z].item,ctx).size()
        <<",\"final_normalized_count\":\""<<chart[normalized(ded,z)]<<"\"}";
    }
    std::cout<<"],\"final_contribution\":\""<<contribution(ded)<<"\"}";
  }
  std::cout<<"],\"found\":"<<found<<",\"Cplusplus_execution\":true,\"physical_weight_test\":false}\n";
  return found==2 && recomputed>=chart[parent] ? 0:1;
}
