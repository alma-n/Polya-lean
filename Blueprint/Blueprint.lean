import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Blueprint.Chapters.RandomWalks
import Blueprint.Chapters.RecurrenceAndTransience
import Blueprint.Chapters.Occupation
import Blueprint.Chapters.GreenFourier
import Blueprint.Chapters.FourierIntegral

set_option linter.dupNamespace false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Pólya's Theorem" =>

:::group "main_result"
Main goal
:::

The goal of this project is to prove that:

> "A drunk man will find his way home, but a drunk bird may get lost forever."

Somewhat more mathematically, the goal is the following:

:::theorem "Polya" (parent := "main_result")
The simple random walk $`X = \big(X(t) \big)_{t \in ℕ}`
on the $`d`-dimensional grid $`ℤ^d` is recurrent if $`d \le 2`
and transient if $`d \, > \, 2`.
:::

{include 0 Blueprint.Chapters.RandomWalks}
{include 0 Blueprint.Chapters.Occupation}
{include 0 Blueprint.Chapters.RecurrenceAndTransience}
{include 0 Blueprint.Chapters.GreenFourier}
{include 0 Blueprint.Chapters.FourierIntegral}

{blueprint_graph}
{blueprint_summary}
