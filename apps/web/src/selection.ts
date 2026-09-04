import { useEffect, useState } from "react";

export const countFromSearch = (search: string): number => {
  const value = new URLSearchParams(search).get("n");
  if (value === null || !/^\d+$/.test(value)) return 68;
  const count = Number(value);
  return Number.isInteger(count) && count >= 1 && count <= 100 ? count : 68;
};

export const useSelection = (): readonly [number, (count: number) => void] => {
  const [count, setCount] = useState(() =>
    countFromSearch(window.location.search),
  );
  useEffect(() => {
    const restore = () => setCount(countFromSearch(window.location.search));
    window.addEventListener("popstate", restore);
    return () => window.removeEventListener("popstate", restore);
  }, []);
  const select = (next: number) => {
    if (next === count) return;
    const url = new URL(window.location.href);
    url.searchParams.set("n", String(next));
    window.history.pushState(null, "", url);
    setCount(next);
  };
  return [count, select];
};
