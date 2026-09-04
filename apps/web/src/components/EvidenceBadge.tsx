import {
  verificationLevel,
  type Claim,
  type VerificationLevel,
} from "@square-packing/domain";
import { BadgeCheck, BookOpen, Cpu, Radio } from "lucide-react";
import { copy } from "../copy.ts";

export const evidencePresentation: Readonly<
  Record<
    VerificationLevel,
    { label: string; className: string; icon: typeof BadgeCheck }
  >
> = {
  "lean-verified": {
    label: copy.verified,
    className: "border-forest/30 bg-forest-soft text-forest",
    icon: BadgeCheck,
  },
  "published-unformalized": {
    label: copy.published,
    className: "border-ochre/25 bg-ochre-soft text-ochre",
    icon: BookOpen,
  },
  "computational-evidence": {
    label: copy.computed,
    className: "border-plum/25 bg-plum-soft text-plum",
    icon: Cpu,
  },
  reported: {
    label: copy.reported,
    className: "border-rule bg-paper text-muted",
    icon: Radio,
  },
};

export const EvidenceBadge = ({ claim }: { claim: Claim }) => {
  const item = evidencePresentation[verificationLevel(claim)];
  const Icon = item.icon;
  return (
    <span
      className={`inline-flex items-center gap-1.5 border px-2 py-1 text-[0.65rem] leading-4 ${item.className}`}
    >
      <Icon className="size-3.5 shrink-0" aria-hidden="true" />
      {item.label}
    </span>
  );
};
