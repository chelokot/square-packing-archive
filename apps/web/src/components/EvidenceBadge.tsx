import {
  verificationLevel,
  type Claim,
  type VerificationLevel,
} from "@square-packing/domain";
import { BadgeCheck, BookOpen, Cpu, Radio } from "lucide-react";

const presentation: Readonly<
  Record<
    VerificationLevel,
    { label: string; className: string; icon: typeof BadgeCheck }
  >
> = {
  "lean-verified": {
    label: "Lean verified",
    className: "border-mint-300/40 bg-mint-300/10 text-mint-300",
    icon: BadgeCheck,
  },
  "published-unformalized": {
    label: "Published · awaiting Lean",
    className: "border-amber-300/35 bg-amber-300/10 text-amber-300",
    icon: BookOpen,
  },
  "computational-evidence": {
    label: "Computed · awaiting Lean",
    className: "border-violet-300/35 bg-violet-300/10 text-violet-300",
    icon: Cpu,
  },
  reported: {
    label: "Reported",
    className: "border-white/15 bg-white/5 text-slate-300",
    icon: Radio,
  },
};

export const EvidenceBadge = ({ claim }: { claim: Claim }) => {
  const item = presentation[verificationLevel(claim)];
  const Icon = item.icon;
  return (
    <span
      className={`inline-flex items-center gap-1.5 rounded-full border px-2.5 py-1 text-[0.68rem] font-semibold tracking-wide ${item.className}`}
    >
      <Icon className="size-3.5" aria-hidden="true" />
      {item.label}
    </span>
  );
};
