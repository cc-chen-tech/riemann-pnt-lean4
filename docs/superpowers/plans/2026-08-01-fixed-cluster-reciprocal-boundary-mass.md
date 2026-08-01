# Fixed-cluster reciprocal boundary-mass implementation plan

1. Import the generic reciprocal fixed-cluster low layer.
2. Combine it with the existing Carlson high-tail boundary-mass limit.
3. Reuse the exact truncated positive-zero split.
4. Prove the eventual positive-zero boundary bound with the improved margin.
5. Add a contract and axiom audit, compile serially, and publish a chained
   Draft PR based on Stack158.
